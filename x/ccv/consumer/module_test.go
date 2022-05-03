package consumer_test

import (
	"fmt"
	"testing"

	sdk "github.com/cosmos/cosmos-sdk/types"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	commitmenttypes "github.com/cosmos/ibc-go/v3/modules/core/23-commitment/types"
	host "github.com/cosmos/ibc-go/v3/modules/core/24-host"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"

	"github.com/cosmos/interchain-security/app"
	"github.com/cosmos/interchain-security/testutil/simapp"
	"github.com/cosmos/interchain-security/x/ccv/consumer"
	"github.com/cosmos/interchain-security/x/ccv/consumer/types"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"

	tmtypes "github.com/tendermint/tendermint/types"

	"github.com/stretchr/testify/suite"
)

func init() {
	ibctesting.DefaultTestingAppInit = simapp.SetupTestingApp
}

type ConsumerTestSuite struct {
	suite.Suite

	coordinator *ibctesting.Coordinator

	// testing chains
	providerChain *ibctesting.TestChain
	consumerChain  *ibctesting.TestChain

	providerClient    *ibctmtypes.ClientState
	providerConsState *ibctmtypes.ConsensusState

	path *ibctesting.Path

	ctx sdk.Context
}

func (suite *ConsumerTestSuite) SetupTest() {
	suite.coordinator = ibctesting.NewCoordinator(suite.T(), 2)
	suite.providerChain = suite.coordinator.GetChain(ibctesting.GetChainID(1))
	suite.consumerChain = suite.coordinator.GetChain(ibctesting.GetChainID(2))

	tmConfig := ibctesting.NewTendermintConfig()

	// commit a block on provider chain before creating client
	suite.coordinator.CommitBlock(suite.providerChain)

	// create client and consensus state of provider chain to initialize consumer chain genesis.
	height := suite.providerChain.LastHeader.GetHeight().(clienttypes.Height)
	UpgradePath := []string{"upgrade", "upgradedIBCState"}

	suite.providerClient = ibctmtypes.NewClientState(
		suite.providerChain.ChainID, tmConfig.TrustLevel, tmConfig.TrustingPeriod, tmConfig.UnbondingPeriod, tmConfig.MaxClockDrift,
		height, commitmenttypes.GetSDKSpecs(), UpgradePath, tmConfig.AllowUpdateAfterExpiry, tmConfig.AllowUpdateAfterMisbehaviour,
	)
	suite.providerConsState = suite.providerChain.LastHeader.ConsensusState()

	// mocking the fact that consumer chain validators should be provider chain validators
	// TODO: Fix testing suite so we can initialize both chains with the same validator set
	valUpdates := tmtypes.TM2PB.ValidatorUpdates(suite.providerChain.Vals)

	params := consumertypes.DefaultParams()
	params.Enabled = true
	consumerGenesis := types.NewInitialGenesisState(suite.providerClient, suite.providerConsState, valUpdates, params)
	suite.consumerChain.App.(*app.App).ConsumerKeeper.InitGenesis(suite.consumerChain.GetContext(), consumerGenesis)

	// create the ccv path and set consumer's clientID to genesis client
	path := ibctesting.NewPath(suite.consumerChain, suite.providerChain)
	path.EndpointA.ChannelConfig.PortID = consumertypes.PortID
	path.EndpointB.ChannelConfig.PortID = providertypes.PortID
	path.EndpointA.ChannelConfig.Version = ccv.Version
	path.EndpointB.ChannelConfig.Version = ccv.Version
	path.EndpointA.ChannelConfig.Order = channeltypes.ORDERED
	path.EndpointB.ChannelConfig.Order = channeltypes.ORDERED
	providerClient, ok := suite.consumerChain.App.(*app.App).ConsumerKeeper.GetProviderClient(suite.consumerChain.GetContext())
	if !ok {
		panic("must already have provider client on consumer chain")
	}
	// set consumer endpoint's clientID
	path.EndpointA.ClientID = providerClient

	// TODO: No idea why or how this works, but it seems that it needs to be done.
	path.EndpointB.Chain.SenderAccount.SetAccountNumber(6)
	path.EndpointA.Chain.SenderAccount.SetAccountNumber(6)

	// create consumer client on provider chain and set as consumer client for consumer chainID in provider keeper.
	path.EndpointB.CreateClient()
	suite.providerChain.App.(*app.App).ProviderKeeper.SetConsumerClient(suite.providerChain.GetContext(), suite.consumerChain.ChainID, path.EndpointB.ClientID)

	suite.coordinator.CreateConnections(path)

	suite.ctx = suite.consumerChain.GetContext()

	suite.path = path
}

func (suite *ConsumerTestSuite) TestOnChanOpenInit() {
	channelID := "channel-1"
	testCases := []struct {
		name     string
		setup    func(suite *ConsumerTestSuite)
		expError bool
	}{
		{
			name: "success",
			setup: func(suite *ConsumerTestSuite) {
				// Set INIT channel on consumer chain
				suite.consumerChain.App.GetIBCKeeper().ChannelKeeper.SetChannel(suite.ctx, consumertypes.PortID, channelID,
					channeltypes.NewChannel(
						channeltypes.INIT, channeltypes.ORDERED, channeltypes.NewCounterparty(providertypes.PortID, ""),
						[]string{suite.path.EndpointA.ConnectionID}, suite.path.EndpointA.ChannelConfig.Version),
				)
				suite.path.EndpointA.ChannelID = channelID
			},
			expError: false,
		},
		{
			name: "invalid: provider channel already established",
			setup: func(suite *ConsumerTestSuite) {
				suite.consumerChain.App.(*app.App).ConsumerKeeper.SetProviderChannel(suite.ctx, "channel-2")
				// Set INIT channel on consumer chain
				suite.consumerChain.App.GetIBCKeeper().ChannelKeeper.SetChannel(suite.ctx, consumertypes.PortID, channelID,
					channeltypes.NewChannel(
						channeltypes.INIT, channeltypes.ORDERED, channeltypes.NewCounterparty(providertypes.PortID, ""),
						[]string{suite.path.EndpointA.ConnectionID}, suite.path.EndpointA.ChannelConfig.Version),
				)
				suite.path.EndpointA.ChannelID = channelID
			},
			expError: true,
		},
		{
			name: "invalid: UNORDERED channel",
			setup: func(suite *ConsumerTestSuite) {
				// set path ORDER to UNORDERED
				suite.path.EndpointA.ChannelConfig.Order = channeltypes.UNORDERED
				// Set INIT channel on consumer chain
				suite.consumerChain.App.GetIBCKeeper().ChannelKeeper.SetChannel(suite.ctx, consumertypes.PortID, channelID,
					channeltypes.NewChannel(
						channeltypes.INIT, channeltypes.UNORDERED, channeltypes.NewCounterparty(providertypes.PortID, ""),
						[]string{suite.path.EndpointA.ConnectionID}, suite.path.EndpointA.ChannelConfig.Version),
				)
				suite.path.EndpointA.ChannelID = channelID
			},
			expError: true,
		},
		{
			name: "invalid: incorrect port",
			setup: func(suite *ConsumerTestSuite) {
				// set path port to invalid portID
				suite.path.EndpointA.ChannelConfig.PortID = "invalidPort"
				// Set INIT channel on consumer chain
				suite.consumerChain.App.GetIBCKeeper().ChannelKeeper.SetChannel(suite.ctx, consumertypes.PortID, channelID,
					channeltypes.NewChannel(
						channeltypes.INIT, channeltypes.UNORDERED, channeltypes.NewCounterparty(providertypes.PortID, ""),
						[]string{suite.path.EndpointA.ConnectionID}, suite.path.EndpointA.ChannelConfig.Version),
				)
				suite.path.EndpointA.ChannelID = channelID
			},
			expError: true,
		},
		{
			name: "invalid: incorrect version",
			setup: func(suite *ConsumerTestSuite) {
				// set path port to invalid version
				suite.path.EndpointA.ChannelConfig.Version = "invalidVersion"
				// Set INIT channel on consumer chain
				suite.consumerChain.App.GetIBCKeeper().ChannelKeeper.SetChannel(suite.ctx, consumertypes.PortID, channelID,
					channeltypes.NewChannel(
						channeltypes.INIT, channeltypes.UNORDERED, channeltypes.NewCounterparty(providertypes.PortID, ""),
						[]string{suite.path.EndpointA.ConnectionID}, suite.path.EndpointA.ChannelConfig.Version),
				)
				suite.path.EndpointA.ChannelID = channelID
			},
			expError: true,
		},
		{
			name: "invalid: verify provider chain failed",
			setup: func(suite *ConsumerTestSuite) {
				// setup a new path with provider client on consumer chain being different from genesis client
				path := ibctesting.NewPath(suite.consumerChain, suite.providerChain)
				path.EndpointA.ChannelConfig.PortID = consumertypes.PortID
				path.EndpointB.ChannelConfig.PortID = providertypes.PortID
				path.EndpointA.ChannelConfig.Version = ccv.Version
				path.EndpointB.ChannelConfig.Version = ccv.Version
				path.EndpointA.ChannelConfig.Order = channeltypes.ORDERED
				path.EndpointB.ChannelConfig.Order = channeltypes.ORDERED

				// create consumer client on provider chain, and provider client on consumer chain
				path.EndpointB.CreateClient()
				path.EndpointA.CreateClient()

				suite.coordinator.CreateConnections(path)
				suite.path = path

				// Set INIT channel on consumer chain
				suite.consumerChain.App.GetIBCKeeper().ChannelKeeper.SetChannel(suite.ctx, consumertypes.PortID, channelID,
					channeltypes.NewChannel(
						channeltypes.INIT, channeltypes.ORDERED, channeltypes.NewCounterparty(providertypes.PortID, ""),
						[]string{suite.path.EndpointA.ConnectionID}, suite.path.EndpointA.ChannelConfig.Version),
				)
				suite.path.EndpointA.ChannelID = channelID
			},
			expError: true,
		},
	}

	for _, tc := range testCases {
		tc := tc
		suite.Run(fmt.Sprintf("Case: %s", tc.name), func() {
			suite.SetupTest() // reset suite
			tc.setup(suite)

			consumerModule := consumer.NewAppModule(suite.consumerChain.App.(*app.App).ConsumerKeeper)
			chanCap, err := suite.consumerChain.App.GetScopedIBCKeeper().NewCapability(suite.ctx, host.ChannelCapabilityPath(consumertypes.PortID, suite.path.EndpointA.ChannelID))
			suite.Require().NoError(err)

			err = consumerModule.OnChanOpenInit(suite.ctx, suite.path.EndpointA.ChannelConfig.Order, []string{suite.path.EndpointA.ConnectionID}, suite.path.EndpointA.ChannelConfig.PortID,
				suite.path.EndpointA.ChannelID, chanCap, channeltypes.NewCounterparty(providertypes.PortID, ""), suite.path.EndpointA.ChannelConfig.Version)

			if tc.expError {
				suite.Require().Error(err)
			} else {
				suite.Require().NoError(err)
			}
		})
	}
}

func (suite *ConsumerTestSuite) TestOnChanOpenTry() {
	// OnOpenTry must error even with correct arguments
	consumerModule := consumer.NewAppModule(suite.consumerChain.App.(*app.App).ConsumerKeeper)
	chanCap, err := suite.consumerChain.App.GetScopedIBCKeeper().NewCapability(suite.ctx, host.ChannelCapabilityPath(consumertypes.PortID, suite.path.EndpointA.ChannelID))
	suite.Require().NoError(err)

	_, err = consumerModule.OnChanOpenTry(suite.ctx, channeltypes.ORDERED, []string{"connection-1"}, consumertypes.PortID, "channel-1", chanCap, channeltypes.NewCounterparty(providertypes.PortID, "channel-1"), ccv.Version)
	suite.Require().Error(err, "OnChanOpenTry callback must error on consumer chain")
}

func (suite *ConsumerTestSuite) TestOnChanOpenAck() {
	channelID := "channel-1"
	testCases := []struct {
		name     string
		setup    func(suite *ConsumerTestSuite)
		expError bool
	}{
		{
			name: "success",
			setup: func(suite *ConsumerTestSuite) {
				// Set INIT channel on consumer chain
				suite.consumerChain.App.GetIBCKeeper().ChannelKeeper.SetChannel(suite.ctx, consumertypes.PortID, channelID,
					channeltypes.NewChannel(
						channeltypes.INIT, channeltypes.ORDERED, channeltypes.NewCounterparty(providertypes.PortID, ""),
						[]string{suite.path.EndpointA.ConnectionID}, suite.path.EndpointA.ChannelConfig.Version),
				)
				suite.path.EndpointA.ChannelID = channelID
			},
			expError: false,
		},
		{
			name: "invalid: provider channel already established",
			setup: func(suite *ConsumerTestSuite) {
				suite.consumerChain.App.(*app.App).ConsumerKeeper.SetProviderChannel(suite.ctx, "channel-2")
				// Set INIT channel on consumer chain
				suite.consumerChain.App.GetIBCKeeper().ChannelKeeper.SetChannel(suite.ctx, consumertypes.PortID, channelID,
					channeltypes.NewChannel(
						channeltypes.INIT, channeltypes.ORDERED, channeltypes.NewCounterparty(providertypes.PortID, ""),
						[]string{suite.path.EndpointA.ConnectionID}, suite.path.EndpointA.ChannelConfig.Version),
				)
				suite.path.EndpointA.ChannelID = channelID
			},
			expError: true,
		},
		{
			name: "invalid: mismatched versions",
			setup: func(suite *ConsumerTestSuite) {
				// Set INIT channel on consumer chain
				suite.consumerChain.App.GetIBCKeeper().ChannelKeeper.SetChannel(suite.ctx, consumertypes.PortID, channelID,
					channeltypes.NewChannel(
						channeltypes.INIT, channeltypes.ORDERED, channeltypes.NewCounterparty(providertypes.PortID, ""),
						[]string{suite.path.EndpointA.ConnectionID}, suite.path.EndpointA.ChannelConfig.Version),
				)
				suite.path.EndpointA.ChannelID = channelID
				// set provider version to invalid version
				suite.path.EndpointB.ChannelConfig.Version = "invalidVersion"
			},
			expError: true,
		},
	}

	for _, tc := range testCases {
		tc := tc
		suite.Run(fmt.Sprintf("Case: %s", tc.name), func() {
			suite.SetupTest() // reset suite
			tc.setup(suite)

			consumerModule := consumer.NewAppModule(suite.consumerChain.App.(*app.App).ConsumerKeeper)

			md := providertypes.HandshakeMetadata{
				ProviderFeePoolAddr: "", // dummy address used
				Version:             suite.path.EndpointB.ChannelConfig.Version,
			}
			mdBz, err := (&md).Marshal()
			suite.Require().NoError(err)

			err = consumerModule.OnChanOpenAck(suite.ctx, consumertypes.PortID, channelID, string(mdBz))
			if tc.expError {
				suite.Require().Error(err)
			} else {
				suite.Require().NoError(err)
			}
		})
	}
}

func (suite *ConsumerTestSuite) TestOnChanOpenConfirm() {
	suite.consumerChain.App.GetIBCKeeper().ChannelKeeper.SetChannel(suite.ctx, consumertypes.PortID, "channel-1",
		channeltypes.NewChannel(
			channeltypes.TRYOPEN, channeltypes.ORDERED, channeltypes.NewCounterparty(providertypes.PortID, "channel-1"),
			[]string{"connection-1"}, ccv.Version,
		))

	consumerModule := consumer.NewAppModule(suite.consumerChain.App.(*app.App).ConsumerKeeper)

	err := consumerModule.OnChanOpenConfirm(suite.ctx, consumertypes.PortID, "channel-1")
	suite.Require().Error(err, "OnChanOpenConfirm must always fail")
}

func (suite *ConsumerTestSuite) TestOnChanCloseInit() {
	channelID := "channel-1"
	testCases := []struct {
		name     string
		setup    func(suite *ConsumerTestSuite)
		expError bool
	}{
		{
			name: "can close duplicate in-progress channel once provider channel is established",
			setup: func(suite *ConsumerTestSuite) {
				// Set INIT channel on consumer chain
				suite.consumerChain.App.GetIBCKeeper().ChannelKeeper.SetChannel(suite.ctx, consumertypes.PortID, channelID,
					channeltypes.NewChannel(
						channeltypes.INIT, channeltypes.ORDERED, channeltypes.NewCounterparty(providertypes.PortID, ""),
						[]string{suite.path.EndpointA.ConnectionID}, suite.path.EndpointA.ChannelConfig.Version),
				)
				suite.path.EndpointA.ChannelID = channelID
				suite.consumerChain.App.(*app.App).ConsumerKeeper.SetProviderChannel(suite.ctx, "different-channel")
			},
			expError: false,
		},
		{
			name: "can close duplicate open channel once provider channel is established",
			setup: func(suite *ConsumerTestSuite) {
				// create open channel
				suite.coordinator.CreateChannels(suite.path)
				suite.consumerChain.App.(*app.App).ConsumerKeeper.SetProviderChannel(suite.ctx, "different-channel")
			},
			expError: false,
		},
		{
			name: "cannot close in-progress channel, no established channel yet",
			setup: func(suite *ConsumerTestSuite) {
				// Set INIT channel on consumer chain
				suite.consumerChain.App.GetIBCKeeper().ChannelKeeper.SetChannel(suite.ctx, consumertypes.PortID, channelID,
					channeltypes.NewChannel(
						channeltypes.INIT, channeltypes.ORDERED, channeltypes.NewCounterparty(providertypes.PortID, ""),
						[]string{suite.path.EndpointA.ConnectionID}, suite.path.EndpointA.ChannelConfig.Version),
				)
				suite.path.EndpointA.ChannelID = channelID
			},
			expError: true,
		},
		{
			name: "cannot close provider channel",
			setup: func(suite *ConsumerTestSuite) {
				// create open channel
				suite.coordinator.CreateChannels(suite.path)
				suite.consumerChain.App.(*app.App).ConsumerKeeper.SetProviderChannel(suite.ctx, suite.path.EndpointA.ChannelID)
			},
			expError: true,
		},
	}

	for _, tc := range testCases {
		tc := tc
		suite.Run(fmt.Sprintf("Case: %s", tc.name), func() {
			suite.SetupTest() // reset suite
			tc.setup(suite)

			consumerModule := consumer.NewAppModule(suite.consumerChain.App.(*app.App).ConsumerKeeper)

			err := consumerModule.OnChanCloseInit(suite.ctx, consumertypes.PortID, suite.path.EndpointA.ChannelID)

			if tc.expError {
				suite.Require().Error(err)
			} else {
				suite.Require().NoError(err)
			}
		})
	}
}

func TestConsumerTestSuite(t *testing.T) {
	suite.Run(t, new(ConsumerTestSuite))
}
