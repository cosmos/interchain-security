package keeper_test

import (
	"fmt"
	"testing"
	"time"

	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"

	"cosmossdk.io/math"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	evidencetypes "github.com/cosmos/cosmos-sdk/x/evidence/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	tmtypes "github.com/cometbft/cometbft/types"

	testkeeper "github.com/cosmos/interchain-security/v3/testutil/keeper"
	"github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
)

// TestJailAndTombstoneValidator tests that the jailing of a validator is only executed
// under the conditions that the validator is neither unbonded, nor jailed, nor tombstoned.
func TestPunishValidator(t *testing.T) {
	pubKey, _ := cryptocodec.FromTmPubKeyInterface(tmtypes.NewMockPV().PrivKey.PubKey())

	// manually build a validator instead of using `stakingtypes.NewValidator`
	// to guarantee that the validator is bonded is jailed for testing

	validator, err := stakingtypes.NewValidator(
		sdk.ValAddress(pubKey.Address().Bytes()),
		pubKey,
		stakingtypes.NewDescription("", "", "", "", ""),
	)
	require.NoError(t, err)

	slashFraction, _ := sdk.NewDecFromStr("0.5")
	consAddr, _ := validator.GetConsAddr()
	providerConsAddr := types.NewProviderConsAddress(consAddr)

	fmt.Println(validator.GetOperator())

	testCases := []struct {
		name          string
		provAddr      types.ProviderConsAddress
		expectedCalls func(sdk.Context, testkeeper.MockedKeepers, types.ProviderConsAddress) []*gomock.Call
		expErr        bool
	}{
		{
			"unfound validator",
			providerConsAddr,
			func(ctx sdk.Context, mocks testkeeper.MockedKeepers,
				provAddr types.ProviderConsAddress,
			) []*gomock.Call {
				return []*gomock.Call{
					// We only expect a single call to GetValidatorByConsAddr.
					// Method will return once validator is not found.
					mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(
						ctx, providerConsAddr.ToSdkConsAddr()).Return(
						stakingtypes.Validator{}, false, // false = Not found.
					).Times(1),
				}
			},
			true,
		},
		{
			"unbonded validator",
			providerConsAddr,
			func(ctx sdk.Context, mocks testkeeper.MockedKeepers,
				provAddr types.ProviderConsAddress,
			) []*gomock.Call {
				return []*gomock.Call{
					// We only expect a single call to GetValidatorByConsAddr.
					mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(
						ctx, providerConsAddr.ToSdkConsAddr()).Return(
						stakingtypes.Validator{Status: stakingtypes.Unbonded}, true,
					).Times(1),
				}
			},
			true,
		},
		{
			"tombstoned validator",
			providerConsAddr,
			func(ctx sdk.Context, mocks testkeeper.MockedKeepers,
				provAddr types.ProviderConsAddress,
			) []*gomock.Call {
				return []*gomock.Call{
					mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(
						ctx, providerConsAddr.ToSdkConsAddr()).Return(
						stakingtypes.Validator{}, true,
					).Times(1),
					mocks.MockSlashingKeeper.EXPECT().IsTombstoned(
						ctx, providerConsAddr.ToSdkConsAddr()).Return(
						true,
					).Times(1),
				}
			},
			true,
		},
		{
			"jailed validator",
			providerConsAddr,
			func(ctx sdk.Context, mocks testkeeper.MockedKeepers,
				provAddr types.ProviderConsAddress,
			) []*gomock.Call {
				validator.Jailed = true
				validator.Status = stakingtypes.Unbonding
				gc := append([]*gomock.Call{
					mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(
						ctx, providerConsAddr.ToSdkConsAddr()).Return(
						validator, true,
					).Times(1),
					mocks.MockSlashingKeeper.EXPECT().IsTombstoned(
						ctx, providerConsAddr.ToSdkConsAddr()).Return(
						false,
					).Times(1),
				},
					testkeeper.GetMocksForSlashValidator(
						ctx,
						mocks,
						validator,
						consAddr,
						[]stakingtypes.UnbondingDelegation{},
						[]stakingtypes.Redelegation{},
						sdk.NewInt(2),
						slashFraction,
						int64(1),
						int64(0),
						int64(1),
					)...,
				)

				gc = append(
					gc,
					mocks.MockSlashingKeeper.EXPECT().JailUntil(
						ctx, providerConsAddr.ToSdkConsAddr(), evidencetypes.DoubleSignJailEndTime).
						Times(1),
					mocks.MockSlashingKeeper.EXPECT().Tombstone(
						ctx, providerConsAddr.ToSdkConsAddr()).
						Times(1),
				)
				return gc
			},
			false,
		},
		{
			"bonded validator",
			providerConsAddr,
			func(ctx sdk.Context, mocks testkeeper.MockedKeepers,
				provAddr types.ProviderConsAddress,
			) []*gomock.Call {
				validator.Jailed = false
				validator.Status = stakingtypes.Bonded
				gc := append([]*gomock.Call{
					mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(
						ctx, providerConsAddr.ToSdkConsAddr()).Return(
						validator, true,
					).Times(1),
					mocks.MockSlashingKeeper.EXPECT().IsTombstoned(
						ctx, providerConsAddr.ToSdkConsAddr()).Return(
						false,
					).Times(1),
				},
					testkeeper.GetMocksForSlashValidator(
						ctx,
						mocks,
						validator,
						consAddr,
						[]stakingtypes.UnbondingDelegation{},
						[]stakingtypes.Redelegation{},
						sdk.NewInt(2),
						slashFraction,
						int64(1),
						int64(0),
						int64(1),
					)...,
				)

				gc = append(
					gc,
					mocks.MockStakingKeeper.EXPECT().Jail(
						ctx, providerConsAddr.ToSdkConsAddr()).
						Times(1),
					mocks.MockSlashingKeeper.EXPECT().JailUntil(
						ctx, providerConsAddr.ToSdkConsAddr(), evidencetypes.DoubleSignJailEndTime).
						Times(1),
					mocks.MockSlashingKeeper.EXPECT().Tombstone(
						ctx, providerConsAddr.ToSdkConsAddr()).
						Times(1),
				)
				return gc
			},
			false,
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			providerKeeper, ctx, _, mocks := testkeeper.GetProviderKeeperAndCtx(
				t, testkeeper.NewInMemKeeperParams(t))

			// Setup expected mock calls
			gomock.InOrder(tc.expectedCalls(ctx, mocks, tc.provAddr)...)

			// Execute method and assert expected mock calls
			err := providerKeeper.PunishValidator(ctx, tc.provAddr)
			if tc.expErr {
				require.Error(t, err)
			} else {
				require.NoError(t, err)
			}
		})
	}
}

// createUndelegation creates an undelegation with `len(initialBalances)` entries
func createUndelegation(initialBalances []int64, completionTimes []time.Time) stakingtypes.UnbondingDelegation {
	var entries []stakingtypes.UnbondingDelegationEntry
	for i, balance := range initialBalances {
		entry := stakingtypes.UnbondingDelegationEntry{
			InitialBalance: sdk.NewInt(balance),
			CompletionTime: completionTimes[i],
		}
		entries = append(entries, entry)
	}

	return stakingtypes.UnbondingDelegation{Entries: entries}
}

// createRedelegation creates a redelegation with `len(initialBalances)` entries
func createRedelegation(initialBalances []int64, completionTimes []time.Time) stakingtypes.Redelegation {
	var entries []stakingtypes.RedelegationEntry
	for i, balance := range initialBalances {
		entry := stakingtypes.RedelegationEntry{
			InitialBalance: sdk.NewInt(balance),
			CompletionTime: completionTimes[i],
		}
		entries = append(entries, entry)
	}

	return stakingtypes.Redelegation{Entries: entries}
}

// TestComputePowerToSlash tests that `ComputePowerToSlash` computes the correct power to be slashed based on
// the tokens in non-mature undelegation and redelegation entries, as well as the current power of the validator
func TestComputePowerToSlash(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// undelegation or redelegation entries with completion time `now` have matured
	now := ctx.BlockHeader().Time
	// undelegation or redelegation entries with completion time one hour in the future have not yet matured
	nowPlus1Hour := now.Add(time.Hour)

	testCases := []struct {
		name           string
		undelegations  []stakingtypes.UnbondingDelegation
		redelegations  []stakingtypes.Redelegation
		power          int64
		powerReduction math.Int
		expectedPower  int64
	}{
		{
			"both undelegations and redelegations 1",
			// 1000 total undelegation tokens
			[]stakingtypes.UnbondingDelegation{
				createUndelegation([]int64{250, 250}, []time.Time{nowPlus1Hour, nowPlus1Hour}),
				createUndelegation([]int64{500}, []time.Time{nowPlus1Hour, nowPlus1Hour}),
			},
			// 1000 total redelegation tokens
			[]stakingtypes.Redelegation{
				createRedelegation([]int64{500}, []time.Time{nowPlus1Hour, nowPlus1Hour}),
				createRedelegation([]int64{250, 250}, []time.Time{nowPlus1Hour, nowPlus1Hour}),
			},
			int64(1000),
			sdk.NewInt(1),
			int64(2000/1 + 1000),
		},
		{
			"both undelegations and redelegations 2",
			// 2000 total undelegation tokens
			[]stakingtypes.UnbondingDelegation{
				createUndelegation([]int64{250, 250}, []time.Time{nowPlus1Hour, nowPlus1Hour}),
				createUndelegation([]int64{}, []time.Time{}),
				createUndelegation([]int64{100, 100}, []time.Time{nowPlus1Hour, nowPlus1Hour}),
				createUndelegation([]int64{800}, []time.Time{nowPlus1Hour}),
				createUndelegation([]int64{500}, []time.Time{nowPlus1Hour}),
			},
			// 3500 total redelegation tokens
			[]stakingtypes.Redelegation{
				createRedelegation([]int64{}, []time.Time{}),
				createRedelegation([]int64{1600}, []time.Time{nowPlus1Hour}),
				createRedelegation([]int64{350, 250}, []time.Time{nowPlus1Hour, nowPlus1Hour}),
				createRedelegation([]int64{700, 200}, []time.Time{nowPlus1Hour, nowPlus1Hour}),
				createRedelegation([]int64{}, []time.Time{}),
				createRedelegation([]int64{400}, []time.Time{nowPlus1Hour}),
			},
			int64(8391),
			sdk.NewInt(2),
			int64((2000+3500)/2 + 8391),
		},
		{
			"no undelegations or redelegations, return provided power",
			[]stakingtypes.UnbondingDelegation{},
			[]stakingtypes.Redelegation{},
			int64(3000),
			sdk.NewInt(5),
			int64(3000), // expectedPower is 0/5 + 3000
		},
		{
			"no undelegations",
			[]stakingtypes.UnbondingDelegation{},
			// 2000 total redelegation tokens
			[]stakingtypes.Redelegation{
				createRedelegation([]int64{}, []time.Time{}),
				createRedelegation([]int64{500}, []time.Time{nowPlus1Hour}),
				createRedelegation([]int64{250, 250}, []time.Time{nowPlus1Hour, nowPlus1Hour}),
				createRedelegation([]int64{700, 200}, []time.Time{nowPlus1Hour, nowPlus1Hour}),
				createRedelegation([]int64{}, []time.Time{}),
				createRedelegation([]int64{100}, []time.Time{nowPlus1Hour}),
			},
			int64(17),
			sdk.NewInt(3),
			int64(2000/3 + 17),
		},
		{
			"no redelegations",
			// 2000 total undelegation tokens
			[]stakingtypes.UnbondingDelegation{
				createUndelegation([]int64{250, 250}, []time.Time{nowPlus1Hour, nowPlus1Hour}),
				createUndelegation([]int64{}, []time.Time{}),
				createUndelegation([]int64{100, 100}, []time.Time{nowPlus1Hour, nowPlus1Hour}),
				createUndelegation([]int64{800}, []time.Time{nowPlus1Hour}),
				createUndelegation([]int64{500}, []time.Time{nowPlus1Hour}),
			},
			[]stakingtypes.Redelegation{},
			int64(1),
			sdk.NewInt(3),
			int64(2000/3 + 1),
		},
		{
			"both (mature) undelegations and redelegations",
			// 2000 total undelegation tokens, 250 + 100 + 500 = 850 of those are from mature undelegations,
			// so 2000 - 850 = 1150
			[]stakingtypes.UnbondingDelegation{
				createUndelegation([]int64{250, 250}, []time.Time{nowPlus1Hour, now}),
				createUndelegation([]int64{}, []time.Time{}),
				createUndelegation([]int64{100, 100}, []time.Time{now, nowPlus1Hour}),
				createUndelegation([]int64{800}, []time.Time{nowPlus1Hour}),
				createUndelegation([]int64{500}, []time.Time{now}),
			},
			// 3500 total redelegation tokens, 350 + 200 + 400 = 950 of those are from mature redelegations
			// so 3500 - 950 = 2550
			[]stakingtypes.Redelegation{
				createRedelegation([]int64{}, []time.Time{}),
				createRedelegation([]int64{1600}, []time.Time{nowPlus1Hour}),
				createRedelegation([]int64{350, 250}, []time.Time{now, nowPlus1Hour}),
				createRedelegation([]int64{700, 200}, []time.Time{nowPlus1Hour, now}),
				createRedelegation([]int64{}, []time.Time{}),
				createRedelegation([]int64{400}, []time.Time{now}),
			},
			int64(8391),
			sdk.NewInt(2),
			int64((1150+2550)/2 + 8391),
		},
	}

	pubKey, _ := cryptocodec.FromTmPubKeyInterface(tmtypes.NewMockPV().PrivKey.PubKey())
	validator, _ := stakingtypes.NewValidator(pubKey.Address().Bytes(), pubKey, stakingtypes.Description{})

	for _, tc := range testCases {
		gomock.InOrder(mocks.MockStakingKeeper.EXPECT().
			SlashUnbondingDelegation(gomock.Any(), gomock.Any(), int64(0), sdk.NewDec(1)).
			DoAndReturn(
				func(_ sdk.Context, undelegation stakingtypes.UnbondingDelegation, _ int64, _ sdk.Dec) math.Int {
					sum := sdk.NewInt(0)
					for _, r := range undelegation.Entries {
						if r.IsMature(ctx.BlockTime()) {
							continue
						}
						sum = sum.Add(sdk.NewInt(r.InitialBalance.Int64()))
					}
					return sum
				}).AnyTimes(),
			mocks.MockStakingKeeper.EXPECT().
				SlashRedelegation(gomock.Any(), gomock.Any(), gomock.Any(), int64(0), sdk.NewDec(1)).
				DoAndReturn(
					func(ctx sdk.Context, _ stakingtypes.Validator, redelegation stakingtypes.Redelegation, _ int64, _ sdk.Dec) math.Int {
						sum := sdk.NewInt(0)
						for _, r := range redelegation.Entries {
							if r.IsMature(ctx.BlockTime()) {
								continue
							}
							sum = sum.Add(sdk.NewInt(r.InitialBalance.Int64()))
						}
						return sum
					}).AnyTimes(),
		)

		actualPower := providerKeeper.ComputePowerToSlash(ctx, validator,
			tc.undelegations, tc.redelegations, tc.power, tc.powerReduction)

		if tc.expectedPower != actualPower {
			require.Fail(t, fmt.Sprintf("\"%s\" failed", tc.name),
				"expected is %d but actual is %d", tc.expectedPower, actualPower)
		}
	}
}

// TestSlashValidator asserts that `SlashValidator` calls the staking module's `Slash` method
// with the correct arguments (i.e., `infractionHeight` of 0 and the expected slash power)
func TestSlashValidator(t *testing.T) {
	keeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// undelegation or redelegation entries with completion time `now` have matured
	now := ctx.BlockHeader().Time
	// undelegation or redelegation entries with completion time one hour in the future have not yet matured
	nowPlus1Hour := now.Add(time.Hour)

	keeperParams := testkeeper.NewInMemKeeperParams(t)
	testkeeper.NewInMemProviderKeeper(keeperParams, mocks)

	pubKey, _ := cryptocodec.FromTmPubKeyInterface(tmtypes.NewMockPV().PrivKey.PubKey())

	validator, err := stakingtypes.NewValidator(
		sdk.ValAddress(pubKey.Address().Bytes()),
		pubKey,
		stakingtypes.NewDescription("", "", "", "", ""),
	)
	require.NoError(t, err)
	validator.Status = stakingtypes.Bonded

	consAddr, _ := validator.GetConsAddr()

	// we create 1000 tokens worth of undelegations, 750 of them are non-matured
	// we also create 1000 tokens worth of redelegations, 750 of them are non-matured
	undelegations := []stakingtypes.UnbondingDelegation{
		createUndelegation([]int64{250, 250}, []time.Time{nowPlus1Hour, now}),
		createUndelegation([]int64{500}, []time.Time{nowPlus1Hour}),
	}
	redelegations := []stakingtypes.Redelegation{
		createRedelegation([]int64{250, 250}, []time.Time{now, nowPlus1Hour}),
		createRedelegation([]int64{500}, []time.Time{nowPlus1Hour}),
	}

	// validator's current power
	currentPower := int64(3000)

	powerReduction := sdk.NewInt(2)
	slashFraction, _ := sdk.NewDecFromStr("0.5")

	// the call to `Slash` should provide an `infractionHeight` of 0 and an expected power of
	// (750 (undelegations) + 750 (redelegations)) / 2 (= powerReduction) + 3000 (currentPower) = 3750
	expectedInfractionHeight := int64(0)
	expectedSlashPower := int64(3750)

	gomock.InOrder(
		testkeeper.GetMocksForSlashValidator(
			ctx,
			mocks,
			validator,
			consAddr,
			undelegations,
			redelegations,
			powerReduction,
			slashFraction,
			currentPower,
			expectedInfractionHeight,
			expectedSlashPower,
		)...,
	)
	keeper.SlashValidator(ctx, validator)
}
