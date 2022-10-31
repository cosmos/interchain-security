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

	consumerTMProtoPublicKey := func() cryptotypes.PubKey {
		_, cpk0 := testutil.GetTMCryptoPublicKeyFromSeed(0)
		ret, err := cryptocodec.FromTmProtoPublicKey(cpk0)
		require.NoError(t, err)
		return ret
	}

	validatorAddressAndStakingType := func() (sdk.ValAddress, stakingtypes.Validator) {
		mockPV, _ := testutil.GetTMCryptoPublicKeyFromSeed(0)
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

	valAddr, val := validatorAddressAndStakingType()

	testCases := []struct {
		name string
		// State-mutating setup specific to this test case
		setup                    func(sdk.Context, keeper.Keeper, testkeeper.MockedKeepers)
		expError                 bool
		chainID                  string
		providerValidatorAddress sdk.ValAddress
		consumerValidatorPubKey  cryptotypes.PubKey
	}{
		{
			name: "success",
			setup: func(ctx sdk.Context,
				k keeper.Keeper, mocks testkeeper.MockedKeepers) {

				k.SetConsumerClientId(ctx, "chainid", "")

				gomock.InOrder(
					mocks.MockStakingKeeper.EXPECT().GetValidator(
						ctx, valAddr,
					).Return(val, true).Times(1),
				)
			},
			expError:                 false,
			chainID:                  "chainid",
			providerValidatorAddress: valAddr,
			consumerValidatorPubKey:  consumerTMProtoPublicKey(),
		},
	}

	for _, tc := range testCases {

		k, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))

		handler := NewHandler(k)

		tc.setup(ctx, k, mocks)

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
