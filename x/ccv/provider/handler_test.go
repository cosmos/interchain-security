package provider_test

import (
	"strings"
	"testing"

	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"
	tmproto "github.com/tendermint/tendermint/proto/tendermint/types"

	"github.com/cosmos/cosmos-sdk/testutil/testdata"
	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	testcrypto "github.com/cosmos/interchain-security/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	"github.com/cosmos/interchain-security/x/ccv/provider"
	keeper "github.com/cosmos/interchain-security/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
)

func TestInvalidMsg(t *testing.T) {
	k, _, _, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	handler := provider.NewHandler(&k)
	res, err := handler(sdk.NewContext(nil, tmproto.Header{}, false, nil), testdata.NewTestMsg())
	require.Error(t, err)
	require.Nil(t, res)
	require.True(t, strings.Contains(err.Error(), "unrecognized provider message type"))
}

func TestAssignConsensusKeyForConsumerChain(t *testing.T) {

	providerCryptoId := testcrypto.NewCryptoIdentityFromIntSeed(0)
	providerConsAddr := providerCryptoId.ProviderConsAddress()

	consumerCryptoId := testcrypto.NewCryptoIdentityFromIntSeed(1)
	consumerConsAddr := consumerCryptoId.ConsumerConsAddress()
	consumerKey := consumerCryptoId.ConsensusSDKPubKey()

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

				gomock.InOrder(
					mocks.MockStakingKeeper.EXPECT().GetValidator(
						ctx, providerCryptoId.SDKValOpAddress(),
						// Return a valid validator, found!
					).Return(providerCryptoId.SDKStakingValidator(), true).Times(1),
					mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx,
						consumerConsAddr.ToSdkConsAddr(),
					).Return(stakingtypes.Validator{}, false),
				)
			},
			expError: false,
			chainID:  "chainid",
		},
		{
			name: "fail: missing validator",
			setup: func(ctx sdk.Context,
				k keeper.Keeper, mocks testkeeper.MockedKeepers) {

				gomock.InOrder(
					mocks.MockStakingKeeper.EXPECT().GetValidator(
						ctx, providerCryptoId.SDKValOpAddress(),
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

				// Use the consumer key already
				k.SetValidatorByConsumerAddr(ctx, "chainid", consumerConsAddr, providerConsAddr)

				gomock.InOrder(
					mocks.MockStakingKeeper.EXPECT().GetValidator(
						ctx, providerCryptoId.SDKValOpAddress(),
						// Return a valid validator, found!
					).Return(providerCryptoId.SDKStakingValidator(), true).Times(1),
					mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx,
						consumerConsAddr.ToSdkConsAddr(),
					).Return(stakingtypes.Validator{}, false),
				)
			},
			expError: true,
			chainID:  "chainid",
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {

			k, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))

			tc.setup(ctx, k, mocks)

			msg, err := providertypes.NewMsgAssignConsumerKey(tc.chainID,
				providerCryptoId.SDKValOpAddress(), consumerKey,
			)

			require.NoError(t, err)

			// Try to handle the message
			_, err = provider.NewHandler(&k)(ctx, msg)

			if tc.expError {
				require.Error(t, err, "invalid case did not return error")
			} else {
				require.NoError(t, err, "valid case returned error")
			}

			ctrl.Finish()
		})
	}
}
