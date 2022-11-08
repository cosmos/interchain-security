package keeper_test

import (
	"testing"

	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"

	"github.com/cosmos/cosmos-sdk/baseapp"
	sdkcodectypes "github.com/cosmos/cosmos-sdk/codec/types"
	"github.com/cosmos/cosmos-sdk/simapp"
	sdktypes "github.com/cosmos/cosmos-sdk/types"
	testcrypto "github.com/cosmos/interchain-security/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	providerkeeper "github.com/cosmos/interchain-security/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
)

func TestGRPCQueryConsumerChainValidatorKeyAssignment(t *testing.T) {

	testValProvider := testcrypto.NewValidatorFromIntSeed(0)
	testValConsumer := testcrypto.NewValidatorFromIntSeed(1)

	testCases := []struct {
		name string
		// State-mutating setup specific to this test case
		setup    func(sdktypes.Context, providerkeeper.Keeper, testkeeper.MockedKeepers, string)
		expError bool
		chainID  string
	}{
		{
			name: "success",
			setup: func(ctx sdktypes.Context, k providerkeeper.Keeper, mocks testkeeper.MockedKeepers, chainID string) {
				// Make chain queryable
				k.SetConsumerClientId(ctx, chainID, "")
				// Make validator queryable
				gomock.InOrder(
					mocks.MockStakingKeeper.EXPECT().GetValidator(
						ctx, testValProvider.SDKValAddress(),
						// Return a valid validator, found
					).Return(testValProvider.SDKStakingValidator(), true).Times(1),
				)
				// Set a mapping
				k.KeyAssignment(ctx, chainID).SetProviderPubKeyToConsumerPubKey(testValProvider.TMProtoCryptoPublicKey(), testValConsumer.TMProtoCryptoPublicKey())
			},
			expError: false,
			chainID:  "chainid",
		},
		{
			name: "mapping doesn't exist",
			setup: func(ctx sdktypes.Context, k providerkeeper.Keeper, mocks testkeeper.MockedKeepers, chainID string) {
				// Make chain queryable
				k.SetConsumerClientId(ctx, chainID, "")
				// Make validator queryable
				gomock.InOrder(
					mocks.MockStakingKeeper.EXPECT().GetValidator(
						ctx, testValProvider.SDKValAddress(),
						// Return a valid validator, found
					).Return(testValProvider.SDKStakingValidator(), true).Times(1),
				)
			},
			expError: true,
			chainID:  "chainid",
		},
	}

	for _, tc := range testCases {

		k, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))

		app := simapp.Setup(false)
		queryHelper := baseapp.NewQueryServerTestHelper(ctx, app.InterfaceRegistry())
		providertypes.RegisterQueryServer(queryHelper, k)
		queryClient := providertypes.NewQueryClient(queryHelper)

		tc.setup(ctx, k, mocks, tc.chainID)

		req := providertypes.QueryConsumerChainValidatorKeyAssignmentRequest{
			ChainId:                  tc.chainID,
			ProviderValidatorAddress: testValProvider.SDKValAddress().String(),
		}

		goCtx := sdktypes.WrapSDKContext(ctx)
		res, err := queryClient.QueryConsumerChainValidatorKeyAssignment(goCtx, &req)

		if tc.expError {
			require.Error(t, err, "invalid case did not return error")
		} else {
			require.NoError(t, err, "valid case returned error")
			consumerValidatorPubKeyAnyExpect, err := sdkcodectypes.NewAnyWithValue(testValConsumer.SDKPubKey())
			require.NoError(t, err, "faulty test")
			require.Equal(t, consumerValidatorPubKeyAnyExpect.Value, res.ConsumerConsensusPubKey.Value)
		}

		ctrl.Finish()
	}
}
