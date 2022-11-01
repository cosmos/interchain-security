package keeper_test

import (
	"testing"

	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	cryptotypes "github.com/cosmos/cosmos-sdk/crypto/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	testutil "github.com/cosmos/interchain-security/testutil/sample"
	keeper "github.com/cosmos/interchain-security/x/ccv/provider/keeper"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
)

func TestGRPCQueryConsumerChainValidatorKeyMapping(t *testing.T) {

	consumerTMProtoPublicKey := func() cryptotypes.PubKey {
		_, cpk0 := testutil.GetTMCryptoPublicKeyFromSeed(0)
		ret, err := cryptocodec.FromTmProtoPublicKey(cpk0)
		require.NoError(t, err)
		return ret
	}

	valAddress := func() sdk.ValAddress {
		mockPV, _ := testutil.GetTMCryptoPublicKeyFromSeed(0)
		tmPubKeyI, err := mockPV.GetPubKey()
		require.NoError(t, err)
		addr, err := sdk.ValAddressFromHex(tmPubKeyI.Address().String())
		require.NoError(t, err)
		return addr
	}

	consumerKey := consumerTMProtoPublicKey()
	valAddr := valAddress()

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
						ctx, valAddr,
						// Return a valid validator, found!
					).Return(valSdkType, true).Times(1),
				)
			},
			expError: false,
			chainID:  "chainid",
		},
	}

	for _, tc := range testCases {

		k, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))

		tc.setup(ctx, k, mocks)

		req := types.QueryConsumerChainValidatorKeyMappingRequest{
			ChainId:                  "chainid",
			ProviderValidatorAddress: valAddr.String(),
		}

		res, err := k.QueryConsumerChainValidatorKeyMapping

		if tc.expError {
			require.Error(t, err, "invalid case did not return error")
		} else {
			require.NoError(t, err, "valid case returned error")
		}

		ctrl.Finish()
	}
}
