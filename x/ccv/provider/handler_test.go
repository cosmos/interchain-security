package provider_test

import (
	"encoding/base64"
	"strings"
	"testing"

	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"

	"github.com/cosmos/cosmos-sdk/testutil/testdata"
	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	tmproto "github.com/cometbft/cometbft/proto/tendermint/types"

	testcrypto "github.com/cosmos/interchain-security/v5/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/v5/testutil/keeper"
	"github.com/cosmos/interchain-security/v5/x/ccv/provider"
	keeper "github.com/cosmos/interchain-security/v5/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
)

func TestInvalidMsg(t *testing.T) {
	k, _, _, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	handler := provider.NewHandler(&k)
	res, err := handler(sdk.NewContext(nil, tmproto.Header{}, false, nil), testdata.NewTestMsg())
	require.Error(t, err)
	require.Nil(t, res)
	require.True(t, strings.Contains(err.Error(), "unrecognized provider message type"))
}

func TestAssignConsensusKeyMsgHandling(t *testing.T) {
	providerCryptoId := testcrypto.NewCryptoIdentityFromIntSeed(0)
	providerConsAddr := providerCryptoId.ProviderConsAddress()

	// a different providerConsAddr, to simulate different validators having assigned keys
	providerCryptoId2 := testcrypto.NewCryptoIdentityFromIntSeed(10)
	providerConsAddr2 := providerCryptoId2.ProviderConsAddress()

	consumerCryptoId := testcrypto.NewCryptoIdentityFromIntSeed(1)
	consumerConsAddr := consumerCryptoId.ConsumerConsAddress()
	consumerKeyBz := base64.StdEncoding.EncodeToString(consumerCryptoId.ConsensusSDKPubKey().Bytes())
	consumerKey := `{"@type":"/cosmos.crypto.ed25519.PubKey","key":"` + consumerKeyBz + `"}`

	testCases := []struct {
		name string
		// State-mutating setup specific to this test case
		setup      func(sdk.Context, keeper.Keeper, testkeeper.MockedKeepers)
		expError   bool
		consumerId string
	}{
		{
			name: "success",
			setup: func(ctx sdk.Context,
				k keeper.Keeper, mocks testkeeper.MockedKeepers,
			) {
				k.SetConsumerPhase(ctx, "consumerId", providertypes.CONSUMER_PHASE_INITIALIZED)
				gomock.InOrder(
					mocks.MockStakingKeeper.EXPECT().GetValidator(
						ctx, providerCryptoId.SDKValOpAddress(),
					).Return(providerCryptoId.SDKStakingValidator(), nil).Times(1),
					mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx,
						consumerConsAddr.ToSdkConsAddr(),
					).Return(stakingtypes.Validator{}, stakingtypes.ErrNoValidatorFound),
				)
			},
			expError:   false,
			consumerId: "consumerId",
		},
		{
			name: "fail: consumer id does not correspond to a registered chain",
			setup: func(ctx sdk.Context,
				k keeper.Keeper, mocks testkeeper.MockedKeepers,
			) {
				gomock.InOrder(
					mocks.MockStakingKeeper.EXPECT().GetValidator(
						ctx, providerCryptoId.SDKValOpAddress(),
						// Return a valid validator, found!
					).Return(providerCryptoId.SDKStakingValidator(), nil).Times(1),
				)
			},
			expError:   true,
			consumerId: "consumerId",
		},
		{
			name: "fail: missing validator",
			setup: func(ctx sdk.Context,
				k keeper.Keeper, mocks testkeeper.MockedKeepers,
			) {
				k.SetConsumerPhase(ctx, "consumerId", providertypes.CONSUMER_PHASE_INITIALIZED)
				gomock.InOrder(
					mocks.MockStakingKeeper.EXPECT().GetValidator(
						ctx, providerCryptoId.SDKValOpAddress(),
					).Return(stakingtypes.Validator{}, stakingtypes.ErrNoValidatorFound).Times(1),
				)
			},
			expError:   true,
			consumerId: "consumerId",
		},
		{
			name: "fail: consumer key in use by other validator",
			setup: func(ctx sdk.Context,
				k keeper.Keeper, mocks testkeeper.MockedKeepers,
			) {
				k.SetConsumerPhase(ctx, "consumerId", providertypes.CONSUMER_PHASE_INITIALIZED)

				// Use the consumer key already used by some other validator
				k.SetValidatorByConsumerAddr(ctx, "consumerId", consumerConsAddr, providerConsAddr2)

				gomock.InOrder(
					mocks.MockStakingKeeper.EXPECT().GetValidator(
						ctx, providerCryptoId.SDKValOpAddress(),
						// validator should not be missing
					).Return(providerCryptoId.SDKStakingValidator(), nil).Times(1),
					mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx,
						consumerConsAddr.ToSdkConsAddr(),
						// return false - no other validator uses the consumer key to validate *on the provider*
					).Return(stakingtypes.Validator{}, nil),
				)
			},
			expError:   true,
			consumerId: "consumerId",
		},
		{
			name: "fail: consumer key in use by the same validator",
			setup: func(ctx sdk.Context,
				k keeper.Keeper, mocks testkeeper.MockedKeepers,
			) {
				k.SetConsumerPhase(ctx, "consumerId", providertypes.CONSUMER_PHASE_INITIALIZED)

				// Use the consumer key already
				k.SetValidatorByConsumerAddr(ctx, "consumerId", consumerConsAddr, providerConsAddr)

				gomock.InOrder(
					mocks.MockStakingKeeper.EXPECT().GetValidator(
						ctx, providerCryptoId.SDKValOpAddress(),
					).Return(providerCryptoId.SDKStakingValidator(), nil).Times(1),
					mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx,
						consumerConsAddr.ToSdkConsAddr(),
					).Return(stakingtypes.Validator{}, stakingtypes.ErrNoValidatorFound),
				)
			},
			expError:   true,
			consumerId: "consumerId",
		},
		{
			name: "fail: consumer key in use by other validator",
			setup: func(ctx sdk.Context,
				k keeper.Keeper, mocks testkeeper.MockedKeepers,
			) {
				k.SetConsumerPhase(ctx, "consumerId", providertypes.CONSUMER_PHASE_INITIALIZED)

				// Use the consumer key already used by some other validator
				k.SetValidatorByConsumerAddr(ctx, "consumerId", consumerConsAddr, providerConsAddr2)

				gomock.InOrder(
					mocks.MockStakingKeeper.EXPECT().GetValidator(
						ctx, providerCryptoId.SDKValOpAddress(),
						// validator should not be missing
					).Return(providerCryptoId.SDKStakingValidator(), nil).Times(1),
					mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx,
						consumerConsAddr.ToSdkConsAddr(),
						// return false - no other validator uses the consumer key to validate *on the provider*
					).Return(stakingtypes.Validator{}, stakingtypes.ErrNoValidatorFound),
				)
			},
			expError:   true,
			consumerId: "consumerId",
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			k, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))

			tc.setup(ctx, k, mocks)
			k.SetConsumerChainId(ctx, tc.consumerId, tc.name)

			msg, err := providertypes.NewMsgAssignConsumerKey(tc.consumerId,
				providerCryptoId.SDKValOpAddress(), consumerKey,
				providerCryptoId.SDKStakingValidator().OperatorAddress,
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
