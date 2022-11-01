package keeper_test

import (
	"testing"

	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"

	"github.com/cosmos/cosmos-sdk/baseapp"
	codectypes "github.com/cosmos/cosmos-sdk/codec/types"
	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	cryptotypes "github.com/cosmos/cosmos-sdk/crypto/types"
	"github.com/cosmos/cosmos-sdk/simapp"
	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	testutil "github.com/cosmos/interchain-security/testutil/sample"
	keeper "github.com/cosmos/interchain-security/x/ccv/provider/keeper"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	tmprotocrypto "github.com/tendermint/tendermint/proto/tendermint/crypto"
)

func TestGRPCQueryConsumerChainValidatorKeyMapping(t *testing.T) {

	consumerKeyData := func() (cryptotypes.PubKey, tmprotocrypto.PublicKey) {
		_, tmprotoPublicKey := testutil.GetTMCryptoPublicKeyFromSeed(0)
		sdkPubKey, err := cryptocodec.FromTmProtoPublicKey(tmprotoPublicKey)
		require.NoError(t, err)
		return sdkPubKey, tmprotoPublicKey
	}

	providerKeyAndValidatorData := func() (sdk.ValAddress, stakingtypes.Validator, tmprotocrypto.PublicKey) {
		mockPV, tmprotoPublicKey := testutil.GetTMCryptoPublicKeyFromSeed(1)
		tmPubKeyI, err := mockPV.GetPubKey()
		require.NoError(t, err)
		sdkPubKeyI, err := cryptocodec.FromTmPubKeyInterface(tmPubKeyI)
		require.NoError(t, err)
		addr, err := sdk.ValAddressFromHex(tmPubKeyI.Address().String())
		require.NoError(t, err)
		consensusAny, err := codectypes.NewAnyWithValue(sdkPubKeyI)
		require.NoError(t, err)
		v := stakingtypes.Validator{ConsensusPubkey: consensusAny}
		return addr, v, tmprotoPublicKey
	}

	consumerSdkPubKeyExpect, consumerTmPublickey := consumerKeyData()
	valSdkAddr, valSdkObject, valTMProtoPublicKey := providerKeyAndValidatorData()

	testCases := []struct {
		name string
		// State-mutating setup specific to this test case
		setup    func(sdk.Context, keeper.Keeper, testkeeper.MockedKeepers, string)
		expError bool
		chainID  string
	}{
		{
			name: "success",
			setup: func(ctx sdk.Context, k keeper.Keeper, mocks testkeeper.MockedKeepers, chainID string) {
				// Make chain queryable
				k.SetConsumerClientId(ctx, chainID, "")
				// Make validator queryable
				gomock.InOrder(
					mocks.MockStakingKeeper.EXPECT().GetValidator(
						ctx, valSdkAddr,
						// Return a valid validator, found!
					).Return(valSdkObject, true).Times(1),
				)
				// Set a mapping
				k.KeyMap(ctx, chainID).SetProviderPubKeyToConsumerPubKey(valTMProtoPublicKey, consumerTmPublickey)
			},
			expError: false,
			chainID:  "chainid",
		},
		{
			name: "mapping doesn't exist",
			setup: func(ctx sdk.Context, k keeper.Keeper, mocks testkeeper.MockedKeepers, chainID string) {
				// Make chain queryable
				k.SetConsumerClientId(ctx, chainID, "")
				// Make validator queryable
				gomock.InOrder(
					mocks.MockStakingKeeper.EXPECT().GetValidator(
						ctx, valSdkAddr,
						// Return a valid validator, found!
					).Return(valSdkObject, true).Times(1),
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
		types.RegisterQueryServer(queryHelper, k)
		queryClient := types.NewQueryClient(queryHelper)

		tc.setup(ctx, k, mocks, tc.chainID)

		req := types.QueryConsumerChainValidatorKeyMappingRequest{
			ChainId:                  tc.chainID,
			ProviderValidatorAddress: valSdkAddr.String(),
		}

		goCtx := sdk.WrapSDKContext(ctx)
		res, err := queryClient.QueryConsumerChainValidatorKeyMapping(goCtx, &req)

		if tc.expError {
			require.Error(t, err, "invalid case did not return error")
		} else {
			require.NoError(t, err, "valid case returned error")
			consumerValidatorPubKeyAnyExpect, err := codectypes.NewAnyWithValue(consumerSdkPubKeyExpect)
			require.NoError(t, err, "faulty test")
			require.Equal(t, consumerValidatorPubKeyAnyExpect.Value, res.ConsumerValidatorPubKey.Value)
		}

		ctrl.Finish()
	}
}
