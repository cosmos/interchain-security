package keeper_test

import (
	"testing"

	sdk "github.com/cosmos/cosmos-sdk/types"
	evidencetypes "github.com/cosmos/cosmos-sdk/x/evidence/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	cryptotestutil "github.com/cosmos/interchain-security/v2/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/v2/testutil/keeper"
	"github.com/cosmos/interchain-security/v2/x/ccv/provider/types"
	"github.com/golang/mock/gomock"
)

func TestJailValidator(t *testing.T) {
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
		providerKeeper.JailValidator(ctx, tc.provAddr)

		ctrl.Finish()
	}
}
