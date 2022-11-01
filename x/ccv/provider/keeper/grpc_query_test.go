package keeper_test

import (
	"strings"
	"testing"

	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"
	tmproto "github.com/tendermint/tendermint/proto/tendermint/types"

	codectypes "github.com/cosmos/cosmos-sdk/codec/types"
	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	cryptotypes "github.com/cosmos/cosmos-sdk/crypto/types"
	"github.com/cosmos/cosmos-sdk/testutil/testdata"
	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	testutil "github.com/cosmos/interchain-security/testutil/sample"
	keeper "github.com/cosmos/interchain-security/x/ccv/provider/keeper"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
)


func TestGRPCQueryConsumerChainValidatorKeyMapping(t *testing.T) {

	testCases := []struct {
		name string
		// State-mutating setup specific to this test case
		setup    func(sdk.Context, keeper.Keeper, testkeeper.MockedKeepers)
		expError bool
		chainID  string
	}{
		{
			name: "success",
			setup: func(ctx sdk.Context, k keeper.Keeper, mocks testkeeper.MockedKeepers) {

				// Make chain queryable
				k.SetConsumerClientId(ctx, "chainid", "")

				gomock.InOrder(
					mocks.MockStakingKeeper.EXPECT().GetValidator(
						ctx, valSdkAddr,
						// Return a valid validator, found!
					).Return(valSdkType, true).Times(1),
				)
			},
			expError: false,
			chainID:  "chainid",
		}
	}

	for _, tc := range testCases {

		k, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))

		tc.setup(ctx, k, mocks)

		msg, err := types.NewMsgDesignateConsensusKeyForConsumerChain(tc.chainID,
			valSdkAddr, consumerTMProtoPublicKey(),
		)

		require.NoError(t, err)

		// Try to handle the message
		_, err = NewHandler(k)(ctx, msg)

		if tc.expError {
			require.Error(t, err, "invalid case did not return error")
		} else {
			require.NoError(t, err, "valid case returned error")
		}

		ctrl.Finish()
	}
}
