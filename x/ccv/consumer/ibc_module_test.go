package consumer_test

import (
	"testing"

	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	"github.com/cosmos/interchain-security/x/ccv/consumer"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	"github.com/stretchr/testify/require"
)

// TODO: OnChanOpenInit

// TODO: OnChanOpenTry

// TODO: OnChanOpenAck

// TestOnChanOpenConfirm validates the consumer's OnChanOpenConfirm implementation against the spec.
//
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-ccf-coconfirm1
// Spec tag: [CCV-CCF-COCONFIRM.1]
func TestOnChanOpenConfirm(t *testing.T) {
	consumerKeeper, ctx, ctrl, _ := testkeeper.GetConsumerKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()
	consumerModule := consumer.NewAppModule(consumerKeeper)

	err := consumerModule.OnChanOpenConfirm(ctx, ccv.ConsumerPortID, "channel-1")
	require.Error(t, err, "OnChanOpenConfirm callback must error on consumer chain")
}

// TestOnChanCloseInit validates the consumer's OnChanCloseInit implementation against the spec.
//
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-ccf-ccinit1
// Spec tag: [CCV-CCF-CCINIT.1]
func TestOnChanCloseInit(t *testing.T) {

	testCases := []struct {
		name                      string
		channelToClose            string
		establishedProviderExists bool
		expPass                   bool
	}{
		{
			name:                      "No established provider channel, error returned disallowing closing of channel",
			channelToClose:            "someChannelID",
			establishedProviderExists: false,
			expPass:                   false,
		},
		{
			name:                      "Provider channel is established, User CANNOT close established provider channel",
			channelToClose:            "provider",
			establishedProviderExists: true,
			expPass:                   false,
		},
		{
			name:                      "User CAN close duplicate channel that is NOT established provider",
			channelToClose:            "someChannelID",
			establishedProviderExists: true,
			expPass:                   true,
		},
	}

	for _, tc := range testCases {
		consumerKeeper, ctx, ctrl, _ := testkeeper.GetConsumerKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
		consumerModule := consumer.NewAppModule(consumerKeeper)

		if tc.establishedProviderExists {
			consumerKeeper.SetProviderChannel(ctx, "provider")
		}

		err := consumerModule.OnChanCloseInit(ctx, "portID", tc.channelToClose)

		if tc.expPass {
			require.NoError(t, err)
		} else {
			require.Error(t, err)
		}
		ctrl.Finish()
	}
}

// TestOnChanCloseConfirm validates the consumer's OnChanCloseConfirm implementation against the spec.
//
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-ccconfirm1// Spec tag: [CCV-CCF-CCINIT.1]
// Spec tag: [CCV-PCF-CCCONFIRM.1]
func TestOnChanCloseConfirm(t *testing.T) {

	consumerKeeper, ctx, ctrl, _ := testkeeper.GetConsumerKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))

	// No external keeper methods should be called
	defer ctrl.Finish()

	consumerModule := consumer.NewAppModule(consumerKeeper)

	// Nothing happens, no error returned
	err := consumerModule.OnChanCloseConfirm(ctx, "portID", "channelID")
	require.NoError(t, err)
}

// Can maybe do these last three in a separate PR, not migrated from e2e anyways
// TODO: OnRecvPacket

// TODO: OnAcknowledgementPacket

// TODO: OnTimeoutPacket
