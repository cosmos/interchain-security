package provider

import (
	"crypto"
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

func key(k uint64) crypto.PublicKey {
	_, pubKey := testutil.GetTMCryptoPublicKeyFromSeed(k)
	return pubKey
}

func TestDesignateConsensusKeyForConsumerChain(t *testing.T) {

	// cpk0 := key(0)
	_, cpk0 := testutil.GetTMCryptoPublicKeyFromSeed(0)
	sdkk, err := cryptocodec.FromTmProtoPublicKey(cpk0)
	require.NoError(t, err)

	mockPV, _ := testutil.GetTMCryptoPublicKeyFromSeed(0)
	tmPubKeyI, err := mockPV.GetPubKey()
	require.NoError(t, err)
	sdkPubKeyI, err := cryptocodec.FromTmPubKeyInterface(tmPubKeyI)
	// mockPV := tmtypes.NewMockPV()
	// pubKey, err := mockPV.GetPubKey()
	require.NoError(t, err)
	addr, err := sdk.ValAddressFromHex(tmPubKeyI.Address().String())
	require.NoError(t, err)

	testCases := []struct {
		name string
		// State-mutating setup specific to this test case
		mockSetup func(sdk.Context,
			keeper.Keeper,
			testkeeper.MockedKeepers, sdk.ValAddress, stakingtypes.Validator)
		expError                 bool
		chainID                  string
		providerValidatorAddress sdk.ValAddress
		consumerValidatorPubKey  cryptotypes.PubKey
	}{
		{
			name: "success",
			mockSetup: func(ctx sdk.Context,
				k keeper.Keeper, mocks testkeeper.MockedKeepers, pva sdk.ValAddress, val stakingtypes.Validator) {

				k.SetConsumerClientId(ctx, "chainid", "")

				gomock.InOrder(
					mocks.MockStakingKeeper.EXPECT().GetValidator(
						ctx, pva,
					).Return(val, true).Times(1),
				)
			},
			expError:                 false,
			chainID:                  "chainid",
			providerValidatorAddress: addr,
			consumerValidatorPubKey:  sdkk,
		},
	}

	for _, tc := range testCases {

		k, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))

		handler := NewHandler(k)

		// _, pubKey := testutil.GetTMCryptoPublicKeyFromSeed(0)
		// consensusAny, err := codectypes.NewAnyWithValue(&tmprotoPublicKey)
		consensusAny, err := codectypes.NewAnyWithValue(sdkPubKeyI)
		require.NoError(t, err)

		// Specific mock setup
		tc.mockSetup(ctx, k, mocks, tc.providerValidatorAddress, stakingtypes.Validator{ConsensusPubkey: consensusAny})

		// Common actions

		msg, err := types.NewMsgDesignateConsensusKeyForConsumerChain("chainId",
			tc.providerValidatorAddress, tc.consumerValidatorPubKey,
		)
		require.NoError(t, err)

		_, err = handler(ctx, msg)

		if tc.expError {
			require.Error(t, err, "invalid case did not return error")
		} else {
			require.NoError(t, err, "valid case returned error")
		}
		ctrl.Finish()
	}
}
