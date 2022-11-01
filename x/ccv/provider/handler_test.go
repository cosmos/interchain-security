package provider

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

func TestInvalidMsg(t *testing.T) {
	k, _, _, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	handler := NewHandler(k)
	res, err := handler(sdk.NewContext(nil, tmproto.Header{}, false, nil), testdata.NewTestMsg())
	require.Error(t, err)
	require.Nil(t, res)
	require.True(t, strings.Contains(err.Error(), "unrecognized provider message type"))
}

func TestDesignateConsensusKeyForConsumerChain(t *testing.T) {

	consumerSdkPubKey := func() cryptotypes.PubKey {
		_, cpk0 := testutil.GetTMCryptoPublicKeyFromSeed(0)
		ret, err := cryptocodec.FromTmProtoPublicKey(cpk0)
		require.NoError(t, err)
		return ret
	}

	valSdkAddressAndValObject := func() (sdk.ValAddress, stakingtypes.Validator) {
		mockPV, _ := testutil.GetTMCryptoPublicKeyFromSeed(1)
		tmPubKeyI, err := mockPV.GetPubKey()
		require.NoError(t, err)
		sdkPubKeyI, err := cryptocodec.FromTmPubKeyInterface(tmPubKeyI)
		require.NoError(t, err)
		addr, err := sdk.ValAddressFromHex(tmPubKeyI.Address().String())
		require.NoError(t, err)
		consensusAny, err := codectypes.NewAnyWithValue(sdkPubKeyI)
		require.NoError(t, err)
		v := stakingtypes.Validator{ConsensusPubkey: consensusAny}
		return addr, v
	}

	valSdkAddr, valSdkObject := valSdkAddressAndValObject()

	testCases := []struct {
		name string
		// State-mutating setup specific to this test case
		setup    func(sdk.Context, keeper.Keeper, testkeeper.MockedKeepers)
		expError bool
		chainID  string
	}{
		{
			name: "success",
			setup: func(ctx sdk.Context,
				k keeper.Keeper, mocks testkeeper.MockedKeepers) {

				// Make chain queryable
				k.SetConsumerClientId(ctx, "chainid", "")

				gomock.InOrder(
					mocks.MockStakingKeeper.EXPECT().GetValidator(
						ctx, valSdkAddr,
						// Return a valid validator, found!
					).Return(valSdkObject, true).Times(1),
				)
			},
			expError: false,
			chainID:  "chainid",
		},
		{
			name: "fail: missing chain",
			setup: func(ctx sdk.Context, k keeper.Keeper, mocks testkeeper.MockedKeepers) {
				// Do not make chain queryable
			},
			expError: true,
			chainID:  "chainid",
		},
		{
			name: "fail: missing validator",
			setup: func(ctx sdk.Context,
				k keeper.Keeper, mocks testkeeper.MockedKeepers) {

				// Make chain queryable
				k.SetConsumerClientId(ctx, "chainid", "")

				gomock.InOrder(
					mocks.MockStakingKeeper.EXPECT().GetValidator(
						ctx, valSdkAddr,
						// return false: not found!
					).Return(stakingtypes.Validator{}, false).Times(1),
				)
			},
			expError: true,
			chainID:  "chainid",
		},
		{
			name: "fail: consumer key in use",
			setup: func(ctx sdk.Context,
				k keeper.Keeper, mocks testkeeper.MockedKeepers) {

				// Make chain queryable
				k.SetConsumerClientId(ctx, "chainid", "")

				tmConsPubKey, err := valSdkObject.TmConsPublicKey()
				require.NoError(t, err)
				tmPubKey, err := cryptocodec.ToTmProtoPublicKey(consumerSdkPubKey())
				require.NoError(t, err)
				// Use the consumer key already
				err = k.KeyMap(ctx, "chainid").SetProviderPubKeyToConsumerPubKey(tmConsPubKey, tmPubKey)
				require.NoError(t, err)

				gomock.InOrder(
					mocks.MockStakingKeeper.EXPECT().GetValidator(
						ctx, valSdkAddr,
					).Return(stakingtypes.Validator{}, false).Times(1),
				)
			},
			expError: true,
			chainID:  "chainid",
		},
	}

	for _, tc := range testCases {

		k, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))

		tc.setup(ctx, k, mocks)

		msg, err := types.NewMsgDesignateConsensusKeyForConsumerChain(tc.chainID,
			valSdkAddr, consumerSdkPubKey(),
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
