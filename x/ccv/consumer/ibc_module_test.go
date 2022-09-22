package consumer_test

import (
	"testing"

	sdk "github.com/cosmos/cosmos-sdk/types"
	capabilitytypes "github.com/cosmos/cosmos-sdk/x/capability/types"
	conntypes "github.com/cosmos/ibc-go/v3/modules/core/03-connection/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	host "github.com/cosmos/ibc-go/v3/modules/core/24-host"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	"github.com/cosmos/interchain-security/x/ccv/consumer"
	consumerkeeper "github.com/cosmos/interchain-security/x/ccv/consumer/keeper"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"
)

// TestOnChanOpenInit validates the consumer's OnChanOpenInit implementation against the spec.
// Additional validation for VerifyProviderChain can be found in it's unit test.
//
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-ccf-coinit1
// Spec tag: [CCV-CCF-COINIT.1]
func TestOnChanOpenInit(t *testing.T) {

	// Params for the OnChanOpenInit method
	type params struct {
		ctx            sdk.Context
		order          channeltypes.Order
		connectionHops []string
		portID         string
		channelID      string
		chanCap        *capabilitytypes.Capability
		counterparty   channeltypes.Counterparty
		version        string
	}

	testCases := []struct {
		name string
		// Test-case specific function that mutates method parameters and setups expected mock calls
		setup   func(sdk.Context, *consumerkeeper.Keeper, *params, testkeeper.MockedKeepers)
		expPass bool
	}{
		{
			"success", func(ctx sdk.Context, keeper *consumerkeeper.Keeper, params *params, mocks testkeeper.MockedKeepers) {
				gomock.InOrder(
					mocks.MockScopedKeeper.EXPECT().ClaimCapability(
						ctx, params.chanCap, host.ChannelCapabilityPath(
							params.portID, params.channelID)).Return(nil).Times(1),
					mocks.MockConnectionKeeper.EXPECT().GetConnection(
						ctx, "connectionIDToProvider").Return(
						conntypes.ConnectionEnd{ClientId: "clientIDToProvider"}, true).Times(1),
				)
			}, true,
		},
		{
			"invalid: channel to provider already established",
			func(ctx sdk.Context, keeper *consumerkeeper.Keeper, params *params, mocks testkeeper.MockedKeepers) {
				keeper.SetProviderChannel(ctx, "existingProviderChanID")
			}, false,
		},
		{
			"invalid: UNORDERED channel",
			func(ctx sdk.Context, keeper *consumerkeeper.Keeper, params *params, mocks testkeeper.MockedKeepers) {
				params.order = channeltypes.UNORDERED
			}, false,
		},
		{
			"invalid port ID, not CCV port",
			func(ctx sdk.Context, keeper *consumerkeeper.Keeper, params *params, mocks testkeeper.MockedKeepers) {
				params.portID = "someDingusPortID"
			}, false,
		},
		{
			"invalid version",
			func(ctx sdk.Context, keeper *consumerkeeper.Keeper, params *params, mocks testkeeper.MockedKeepers) {
				params.version = "someDingusVer"
			}, false,
		},
		{
			"invalid counterparty port ID",
			func(ctx sdk.Context, keeper *consumerkeeper.Keeper, params *params, mocks testkeeper.MockedKeepers) {
				params.counterparty.PortId = "someOtherDingusPortID"
			}, false,
		},
		{
			"invalid clientID to provider",
			func(ctx sdk.Context, keeper *consumerkeeper.Keeper, params *params, mocks testkeeper.MockedKeepers) {
				gomock.InOrder(
					mocks.MockScopedKeeper.EXPECT().ClaimCapability(
						ctx, params.chanCap, host.ChannelCapabilityPath(
							params.portID, params.channelID)).Return(nil).Times(1),
					mocks.MockConnectionKeeper.EXPECT().GetConnection(
						ctx, "connectionIDToProvider").Return(
						conntypes.ConnectionEnd{ClientId: "unexpectedClientID"}, true).Times(1), // unexpected clientID
				)
			}, false,
		},
	}

	for _, tc := range testCases {

		// Common setup
		consumerKeeper, ctx, ctrl, mocks := testkeeper.GetConsumerKeeperAndCtx(
			t, testkeeper.NewInMemKeeperParams(t))
		consumerModule := consumer.NewAppModule(consumerKeeper)

		consumerKeeper.SetPort(ctx, ccv.ConsumerPortID)
		consumerKeeper.SetProviderClientID(ctx, "clientIDToProvider")

		// Instantiate valid params as default. Individual test cases mutate these as needed.
		params := params{
			ctx:            ctx,
			order:          channeltypes.ORDERED,
			connectionHops: []string{"connectionIDToProvider"},
			portID:         ccv.ConsumerPortID,
			channelID:      "consumerChannelID",
			chanCap:        &capabilitytypes.Capability{},
			counterparty:   channeltypes.NewCounterparty(ccv.ProviderPortID, "providerChannelID"),
			version:        ccv.Version,
		}

		tc.setup(ctx, &consumerKeeper, &params, mocks)

		err := consumerModule.OnChanOpenInit(
			params.ctx,
			params.order,
			params.connectionHops,
			params.portID,
			params.channelID,
			params.chanCap,
			params.counterparty,
			params.version,
		)

		if tc.expPass {
			require.NoError(t, err)
		} else {
			require.Error(t, err)
		}
		// Confirm there are no unexpected external keeper calls
		ctrl.Finish()
	}
}

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
