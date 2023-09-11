package keeper_test

import (
	"fmt"
	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	evidencetypes "github.com/cosmos/cosmos-sdk/x/evidence/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	cryptotestutil "github.com/cosmos/interchain-security/v2/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/v2/testutil/keeper"
	"github.com/cosmos/interchain-security/v2/x/ccv/provider/types"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"
	tmtypes "github.com/tendermint/tendermint/types"
	"testing"
	"time"
)

// FIXME: break the JailAndTombstoneValidator function into two ... seems complicated to do both at once
// TestJailAndTombstoneValidator tests that the jailing of a validator is only executed
// under the conditions that the validator is neither unbonded, already jailed, nor tombstoned.
func TestJailAndTombstoneValidator(t *testing.T) {
	providerConsAddr := cryptotestutil.NewCryptoIdentityFromIntSeed(7842334).ProviderConsAddress()
	testCases := []struct {
		name          string
		provAddr      types.ProviderConsAddress
		expectedCalls func(sdk.Context, testkeeper.MockedKeepers, types.ProviderConsAddress) []*gomock.Call
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
		},
		{
			"jailed validator",
			providerConsAddr,
			func(ctx sdk.Context, mocks testkeeper.MockedKeepers,
				provAddr types.ProviderConsAddress,
			) []*gomock.Call {
				return []*gomock.Call{
					mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(
						ctx, providerConsAddr.ToSdkConsAddr()).Return(
						stakingtypes.Validator{Jailed: true}, true,
					).Times(1),
					mocks.MockSlashingKeeper.EXPECT().IsTombstoned(
						ctx, providerConsAddr.ToSdkConsAddr()).Return(
						false,
					).Times(1),
					mocks.MockSlashingKeeper.EXPECT().JailUntil(
						ctx, providerConsAddr.ToSdkConsAddr(), evidencetypes.DoubleSignJailEndTime).
						Times(1),
				}
			},
		},
		{
			"bonded validator",
			providerConsAddr,
			func(ctx sdk.Context, mocks testkeeper.MockedKeepers,
				provAddr types.ProviderConsAddress,
			) []*gomock.Call {
				return []*gomock.Call{
					mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(
						ctx, providerConsAddr.ToSdkConsAddr()).Return(
						stakingtypes.Validator{Status: stakingtypes.Bonded}, true,
					).Times(1),
					mocks.MockSlashingKeeper.EXPECT().IsTombstoned(
						ctx, providerConsAddr.ToSdkConsAddr()).Return(
						false,
					).Times(1),
					mocks.MockStakingKeeper.EXPECT().Jail(
						ctx, providerConsAddr.ToSdkConsAddr()).
						Times(1),
					mocks.MockSlashingKeeper.EXPECT().JailUntil(
						ctx, providerConsAddr.ToSdkConsAddr(), evidencetypes.DoubleSignJailEndTime).
						Times(1),
				}
			},
		},
	}

	for _, tc := range testCases {
		providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(
			t, testkeeper.NewInMemKeeperParams(t))

		// Setup expected mock calls
		gomock.InOrder(tc.expectedCalls(ctx, mocks, tc.provAddr)...)

		// Execute method and assert expected mock calls
		providerKeeper.JailAndTombstoneValidator(ctx, tc.provAddr)

		ctrl.Finish()
	}
}

func createUndelegation(tokensPerEntry []int64) stakingtypes.UnbondingDelegation {
	var entries []stakingtypes.UnbondingDelegationEntry
	for _, t := range tokensPerEntry {
		entry := stakingtypes.UnbondingDelegationEntry{
			InitialBalance: sdk.NewInt(t),
		}
		entries = append(entries, entry)
	}

	return stakingtypes.UnbondingDelegation{Entries: entries}
}

func createRedelegation(tokensPerEntry []int64) stakingtypes.Redelegation {
	var entries []stakingtypes.RedelegationEntry
	for _, t := range tokensPerEntry {
		entry := stakingtypes.RedelegationEntry{
			InitialBalance: sdk.NewInt(t),
		}
		entries = append(entries, entry)
	}

	return stakingtypes.Redelegation{Entries: entries}
}

func TestComputePowerToSlash(t *testing.T) {
	providerKeeper, _, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	testCases := []struct {
		name           string
		undelegations  []stakingtypes.UnbondingDelegation
		redelegations  []stakingtypes.Redelegation
		power          int64
		powerReduction sdk.Int
		expectedPower  int64
	}{
		{
			"both undelegations and redelegations 1",
			// 1000 total undelegation tokens
			[]stakingtypes.UnbondingDelegation{
				createUndelegation([]int64{250, 250}),
				createUndelegation([]int64{500})},
			// 1000 total redelegation tokens
			[]stakingtypes.Redelegation{
				createRedelegation([]int64{500}),
				createRedelegation([]int64{250, 250}),
			},
			int64(1000),
			sdk.NewInt(1),
			int64(2000/1 + 1000),
		},
		{
			"both undelegations and redelegations 2",
			// 2000 total undelegation tokens
			[]stakingtypes.UnbondingDelegation{
				createUndelegation([]int64{250, 250}),
				createUndelegation([]int64{}),
				createUndelegation([]int64{100, 100}),
				createUndelegation([]int64{800}),
				createUndelegation([]int64{500})},
			// 3500 total redelegation tokens
			[]stakingtypes.Redelegation{
				createRedelegation([]int64{}),
				createRedelegation([]int64{1600}),
				createRedelegation([]int64{350, 250}),
				createRedelegation([]int64{700, 200}),
				createRedelegation([]int64{}),
				createRedelegation([]int64{400}),
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
			int64(0/5 + 3000),
		},
		{
			"no undelegations",
			[]stakingtypes.UnbondingDelegation{},
			// 2000 total redelegation tokens
			[]stakingtypes.Redelegation{
				createRedelegation([]int64{}),
				createRedelegation([]int64{500}),
				createRedelegation([]int64{250, 250}),
				createRedelegation([]int64{700, 200}),
				createRedelegation([]int64{}),
				createRedelegation([]int64{100}),
			},
			int64(17),
			sdk.NewInt(3),
			int64(2000/3 + 17),
		},
		{
			"no redelegations",
			// 2000 total undelegation tokens
			[]stakingtypes.UnbondingDelegation{
				createUndelegation([]int64{250, 250}),
				createUndelegation([]int64{}),
				createUndelegation([]int64{100, 100}),
				createUndelegation([]int64{800}),
				createUndelegation([]int64{500})},
			[]stakingtypes.Redelegation{},
			int64(1),
			sdk.NewInt(3),
			int64(2000/3 + 1),
		},
	}

	for _, tc := range testCases {
		actualPower := providerKeeper.ComputePowerToSlash(tc.undelegations, tc.redelegations, tc.power, tc.powerReduction)
		if tc.expectedPower != actualPower {
			require.Fail(t, fmt.Sprintf("\"%s\" failed", tc.name),
				"expected is %d but actual is %d", tc.expectedPower, actualPower)
		}
	}
}

// FIXME: Probably the following test could be a combination with computePowertoSlash ...
// Not sure I like this
// the actual slashing should be checked from integration tests
// TestSlashValidator asserts that `SlashValidator` calls the staking module's `Slash` method
// with the correct arguments (i.e., `infractionHeight` of 0 and the expected slash power)
func TestSlashValidator(t *testing.T) {
	keeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	ctx = ctx.WithBlockTime(time.Now())
	keeperParams := testkeeper.NewInMemKeeperParams(t)
	testkeeper.NewInMemProviderKeeper(keeperParams, mocks)

	pubKey, _ := cryptocodec.FromTmPubKeyInterface(tmtypes.NewMockPV().PrivKey.PubKey())

	validator, _ := stakingtypes.NewValidator(pubKey.Address().Bytes(), pubKey, stakingtypes.Description{})
	consAddr, _ := validator.GetConsAddr()
	providerAddr := types.NewProviderConsAddress(consAddr)

	// we create 1000 tokens worth of undelegations and 1000 tokens worth of redelegations
	undelegations := []stakingtypes.UnbondingDelegation{
		createUndelegation([]int64{250, 250}),
		createUndelegation([]int64{500})}
	redelegations := []stakingtypes.Redelegation{
		createRedelegation([]int64{250, 250}),
		createRedelegation([]int64{500})}

	// validator's current power
	currentPower := int64(3000)

	powerReduction := sdk.NewInt(2)
	slashFraction, _ := sdk.NewDecFromStr("0.5")

	// the call to `Slash` should provide an `infractionHeight` of 0 and an expected power of
	// (1000 (undelegations) + 1000 (redelegations)) / 2 (= powerReduction) + 3000 (currentPower) = 4000
	expectedInfractionHeight := int64(0)
	expectedSlashPower := int64(4000)

	expectedCalls := []*gomock.Call{
		mocks.MockStakingKeeper.EXPECT().
			GetValidatorByConsAddr(ctx, gomock.Any()).
			Return(validator, true),
		mocks.MockSlashingKeeper.EXPECT().
			IsTombstoned(ctx, consAddr).
			Return(false),
		mocks.MockStakingKeeper.EXPECT().
			GetUnbondingDelegationsFromValidator(ctx, validator.GetOperator()).
			Return(undelegations),
		mocks.MockStakingKeeper.EXPECT().
			GetRedelegationsFromSrcValidator(ctx, validator.GetOperator()).
			Return(redelegations),
		mocks.MockStakingKeeper.EXPECT().
			GetLastValidatorPower(ctx, validator.GetOperator()).
			Return(currentPower),
		mocks.MockStakingKeeper.EXPECT().
			PowerReduction(ctx).
			Return(powerReduction),
		mocks.MockSlashingKeeper.EXPECT().
			SlashFractionDoubleSign(ctx).
			Return(slashFraction),
		mocks.MockStakingKeeper.EXPECT().
			Slash(ctx, consAddr, expectedInfractionHeight, expectedSlashPower, slashFraction, stakingtypes.DoubleSign).
			Times(1),
	}

	gomock.InOrder(expectedCalls...)
	keeper.SlashValidator(ctx, providerAddr)
}
