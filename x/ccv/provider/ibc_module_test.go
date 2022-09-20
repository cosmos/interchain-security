package provider_test

import (
	"testing"

	sdk "github.com/cosmos/cosmos-sdk/types"
	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"
	capabilitytypes "github.com/cosmos/cosmos-sdk/x/capability/types"
	conntypes "github.com/cosmos/ibc-go/v3/modules/core/03-connection/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	host "github.com/cosmos/ibc-go/v3/modules/core/24-host"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	"github.com/cosmos/interchain-security/x/ccv/provider"
	providerkeeper "github.com/cosmos/interchain-security/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"
)

// TestOnChanOpenInit tests the provider's OnChanOpenInit method against spec.
//
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-coinit1
// Spec Tag: [CCV-PCF-COINIT.1]
func TestOnChanOpenInit(t *testing.T) {

	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(
		t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()
	providerModule := provider.NewAppModule(&providerKeeper)

	// OnChanOpenInit must error for provider even with correct arguments
	err := providerModule.OnChanOpenInit(
		ctx,
		channeltypes.ORDERED,
		[]string{"connection-1"},
		ccv.ProviderPortID,
		"channel-1",
		nil,
		channeltypes.NewCounterparty(ccv.ConsumerPortID, "channel-1"),
		ccv.Version,
	)
	require.Error(t, err, "OnChanOpenInit must error on provider chain")
}

// TestOnChanOpenTry validates the provider's OnChanOpenTry implementation against the spec.
//
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-cotry1
// Spec tag: [CCV-PCF-COTRY.1]
func TestOnChanOpenTry(t *testing.T) {

	// Params for the ChanOpenTry method
	type params struct {
		ctx                 sdk.Context
		order               channeltypes.Order
		connectionHops      []string
		portID              string
		channelID           string
		chanCap             *capabilitytypes.Capability
		counterparty        channeltypes.Counterparty
		counterpartyVersion string
	}

	testCases := []struct {
		name         string
		mutateParams func(*params, *providerkeeper.Keeper)
		expPass      bool
	}{
		{
			"success", func(*params, *providerkeeper.Keeper) {}, true,
		},
		{
			"invalid order", func(params *params, keeper *providerkeeper.Keeper) {
				params.order = channeltypes.UNORDERED
			}, false,
		},
		{
			"invalid port ID", func(params *params, keeper *providerkeeper.Keeper) {
				params.portID = "bad port"
			}, false,
		},
		{
			"invalid counter party port ID", func(params *params, keeper *providerkeeper.Keeper) {
				params.counterparty.PortId = "bad port"
			}, false,
		},
		{
			"invalid counter party version", func(params *params, keeper *providerkeeper.Keeper) {
				params.counterpartyVersion = "invalidVersion"
			}, false,
		},
		{
			"unexpected client ID mapped to chain ID", func(params *params, keeper *providerkeeper.Keeper) {
				keeper.SetConsumerClientId(
					params.ctx,
					"consumerChainID",
					"invalidClientID",
				)
			}, false,
		},
		{
			"other CCV channel exists for this consumer chain",
			func(params *params, keeper *providerkeeper.Keeper) {
				keeper.SetChainToChannel(
					params.ctx,
					"consumerChainID",
					"some existing channel ID",
				)
			}, false,
		},
	}

	for _, tc := range testCases {

		// Setup
		providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(
			t, testkeeper.NewInMemKeeperParams(t))
		providerModule := provider.NewAppModule(&providerKeeper)

		providerKeeper.SetPort(ctx, "providerPortID")
		providerKeeper.SetConsumerClientId(ctx, "consumerChainID", "clientIDToConsumer")

		// Instantiate valid params as default. Individual test cases mutate these as needed.
		params := params{
			ctx:                 ctx,
			order:               channeltypes.ORDERED,
			connectionHops:      []string{"connectionIDToConsumer"},
			portID:              "providerPortID",
			channelID:           "providerChannelID",
			chanCap:             &capabilitytypes.Capability{},
			counterparty:        channeltypes.NewCounterparty(ccv.ConsumerPortID, "consumerChannelID"),
			counterpartyVersion: ccv.Version,
		}

		// Expected mock calls
		moduleAcct := authtypes.ModuleAccount{BaseAccount: &authtypes.BaseAccount{}}
		moduleAcct.BaseAccount.Address = authtypes.NewModuleAddress(authtypes.FeeCollectorName).String()

		// Number of calls is not asserted, since not all code paths are hit for failures
		gomock.InOrder(
			mocks.MockScopedKeeper.EXPECT().ClaimCapability(
				params.ctx, params.chanCap, host.ChannelCapabilityPath(params.portID, params.channelID)).AnyTimes(),
			mocks.MockConnectionKeeper.EXPECT().GetConnection(ctx, "connectionIDToConsumer").Return(
				conntypes.ConnectionEnd{ClientId: "clientIDToConsumer"}, true,
			).AnyTimes(),
			mocks.MockClientKeeper.EXPECT().GetClientState(ctx, "clientIDToConsumer").Return(
				&ibctmtypes.ClientState{ChainId: "consumerChainID"}, true,
			).AnyTimes(),
			mocks.MockAccountKeeper.EXPECT().GetModuleAccount(ctx, "").Return(&moduleAcct).AnyTimes(),
		)

		tc.mutateParams(&params, &providerKeeper)

		metadata, err := providerModule.OnChanOpenTry(
			params.ctx,
			params.order,
			params.connectionHops,
			params.portID,
			params.channelID,
			params.chanCap,
			params.counterparty,
			params.counterpartyVersion,
		)

		if tc.expPass {
			require.NoError(t, err)
			md := &providertypes.HandshakeMetadata{}
			err = md.Unmarshal([]byte(metadata))
			require.NoError(t, err)
			require.Equal(t, moduleAcct.BaseAccount.Address, md.ProviderFeePoolAddr,
				"returned dist account metadata must match expected")
			require.Equal(t, ccv.Version, md.Version, "returned ccv version metadata must match expected")
			ctrl.Finish()
		} else {
			require.Error(t, err)
			// See if you can allow ctrl not to finish like this?
			ctrl = nil
		}
	}
}

// OnChanOpenAck for provider (doesn't exist)

// OnChanOpenConfirm for provider (doesn't exist)
