package e2e_test

import (
	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"

	app "github.com/cosmos/interchain-security/app/consumer"

	"fmt"

	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	tmtypes "github.com/tendermint/tendermint/types"

	"github.com/cosmos/interchain-security/x/ccv/utils"

	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	host "github.com/cosmos/ibc-go/v3/modules/core/24-host"

	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	"github.com/cosmos/interchain-security/x/ccv/consumer"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"

	abci "github.com/tendermint/tendermint/abci/types"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"
	appProvider "github.com/cosmos/interchain-security/app/provider"
)

func (suite *ConsumerKeeperTestSuite) TestConsumerGenesis() {
	genesis := suite.consumerChain.App.(*app.App).ConsumerKeeper.ExportGenesis(suite.consumerChain.GetContext())

	suite.Require().Equal(suite.providerClient, genesis.ProviderClientState)
	suite.Require().Equal(suite.providerConsState, genesis.ProviderConsensusState)

	suite.Require().NotPanics(func() {
		suite.consumerChain.App.(*app.App).ConsumerKeeper.InitGenesis(suite.consumerChain.GetContext(), genesis)
		// reset suite to reset provider client
		suite.SetupTest()
	})

	ctx := suite.consumerChain.GetContext()
	portId := suite.consumerChain.App.(*app.App).ConsumerKeeper.GetPort(ctx)
	suite.Require().Equal(ccv.ConsumerPortID, portId)

	clientId, ok := suite.consumerChain.App.(*app.App).ConsumerKeeper.GetProviderClientID(ctx)
	suite.Require().True(ok)
	clientState, ok := suite.consumerChain.App.GetIBCKeeper().ClientKeeper.GetClientState(ctx, clientId)
	suite.Require().True(ok)
	suite.Require().Equal(genesis.ProviderClientState, clientState, "client state not set correctly after InitGenesis")

	suite.SetupCCVChannel()

	origTime := suite.consumerChain.GetContext().BlockTime()

	pk1, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
	suite.Require().NoError(err)
	pk2, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
	suite.Require().NoError(err)
	pd := ccv.NewValidatorSetChangePacketData(
		[]abci.ValidatorUpdate{
			{
				PubKey: pk1,
				Power:  30,
			},
			{
				PubKey: pk2,
				Power:  20,
			},
		},
		1,
		nil,
	)
	packet := channeltypes.NewPacket(pd.GetBytes(), 1,
		ccv.ProviderPortID, suite.path.EndpointB.ChannelID,
		ccv.ConsumerPortID, suite.path.EndpointA.ChannelID,
		clienttypes.NewHeight(1, 0), 0)
	suite.consumerChain.App.(*app.App).ConsumerKeeper.OnRecvVSCPacket(suite.consumerChain.GetContext(), packet, pd)

	// mocking the fact that consumer chain validators should be provider chain validators
	// TODO: Fix testing suite so we can initialize both chains with the same validator set
	valUpdates := tmtypes.TM2PB.ValidatorUpdates(suite.providerChain.Vals)

	restartGenesis := suite.consumerChain.App.(*app.App).ConsumerKeeper.ExportGenesis(suite.consumerChain.GetContext())
	restartGenesis.InitialValSet = valUpdates

	// ensure reset genesis is set correctly
	providerChannel := suite.path.EndpointA.ChannelID
	suite.Require().Equal(providerChannel, restartGenesis.ProviderChannelId)
	maturityTime := suite.consumerChain.App.(*app.App).ConsumerKeeper.GetPacketMaturityTime(suite.consumerChain.GetContext(), 1)
	unbondingPeriod, found := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetUnbondingTime(suite.ctx)
	suite.Require().True(found)
	suite.Require().Equal(uint64(origTime.Add(unbondingPeriod).UnixNano()), maturityTime, "maturity time is not set correctly in genesis")

	suite.Require().NotPanics(func() {
		suite.consumerChain.App.(*app.App).ConsumerKeeper.InitGenesis(suite.consumerChain.GetContext(), restartGenesis)
	})
}

// TestProviderClientMatches tests that the provider client managed by the consumer keeper matches the client keeper's client state
func (suite *ConsumerKeeperTestSuite) TestProviderClientMatches() {
	providerClientID, ok := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetProviderClientID(suite.ctx)
	suite.Require().True(ok)

	clientState, _ := suite.consumerChain.App.GetIBCKeeper().ClientKeeper.GetClientState(suite.ctx, providerClientID)
	suite.Require().Equal(suite.providerClient, clientState, "stored client state does not match genesis provider client")
}

// TODO: unit and spec tags
func (suite *ConsumerTestSuite) TestOnChanOpenInit() {
	var (
		channel *channeltypes.Channel
	)

	testCases := []struct {
		name     string
		malleate func()
		expPass  bool
	}{

		{
			"success", func() {}, true,
		},
		{
			"invalid: provider channel already established", func() {
				suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.SetProviderChannel(suite.ctx, "channel-2")
			}, false,
		},
		{
			"invalid: UNORDERED channel", func() {
				channel.Ordering = channeltypes.UNORDERED
			}, false,
		},
		{
			"invalid port ID", func() {
				suite.path.EndpointA.ChannelConfig.PortID = ibctesting.MockPort
			}, false,
		},
		{
			"invalid version", func() {
				channel.Version = "version"
			}, false,
		},
		{
			"invalid counter party port ID", func() {
				channel.Counterparty.PortId = ibctesting.MockPort
			}, false,
		},
		{
			"invalid: verify provider chain failed", func() {
				// setup a new path with provider client on consumer chain being different from genesis client
				path := ibctesting.NewPath(suite.consumerChain, suite.providerChain)
				// - channel config
				path.EndpointA.ChannelConfig.PortID = ccv.ConsumerPortID
				path.EndpointB.ChannelConfig.PortID = ccv.ProviderPortID
				path.EndpointA.ChannelConfig.Version = ccv.Version
				path.EndpointB.ChannelConfig.Version = ccv.Version
				path.EndpointA.ChannelConfig.Order = channeltypes.ORDERED
				path.EndpointB.ChannelConfig.Order = channeltypes.ORDERED

				// create consumer client on provider chain, and provider client on consumer chain
				providerUnbondingPeriod := suite.providerChain.App.(*appProvider.App).GetStakingKeeper().UnbondingTime(suite.providerChain.GetContext())
				consumerUnbondingPeriod := utils.ComputeConsumerUnbondingPeriod(providerUnbondingPeriod)
				err := suite.createCustomClient(path.EndpointB, consumerUnbondingPeriod)
				suite.Require().NoError(err)
				err = suite.createCustomClient(path.EndpointA, providerUnbondingPeriod)
				suite.Require().NoError(err)

				suite.coordinator.CreateConnections(path)
				suite.path = path
				channel.ConnectionHops = []string{suite.path.EndpointA.ConnectionID}
			}, false,
		},
	}

	for _, tc := range testCases {
		tc := tc

		suite.Run(tc.name, func() {
			suite.SetupTest() // reset

			suite.path.EndpointA.ChannelID = ibctesting.FirstChannelID

			counterparty := channeltypes.NewCounterparty(suite.path.EndpointB.ChannelConfig.PortID, "")
			channel = &channeltypes.Channel{
				State:          channeltypes.INIT,
				Ordering:       channeltypes.ORDERED,
				Counterparty:   counterparty,
				ConnectionHops: []string{suite.path.EndpointA.ConnectionID},
				Version:        ccv.Version,
			}

			consumerModule := consumer.NewAppModule(suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper)
			chanCap, err := suite.consumerChain.App.GetScopedIBCKeeper().NewCapability(
				suite.ctx,
				host.ChannelCapabilityPath(
					ccv.ConsumerPortID,
					suite.path.EndpointA.ChannelID,
				),
			)
			suite.Require().NoError(err)

			tc.malleate() // explicitly change fields in channel and testChannel

			err = consumerModule.OnChanOpenInit(
				suite.ctx,
				channel.Ordering,
				channel.GetConnectionHops(),
				suite.path.EndpointA.ChannelConfig.PortID,
				suite.path.EndpointA.ChannelID,
				chanCap,
				channel.Counterparty,
				channel.GetVersion(),
			)

			if tc.expPass {
				suite.Require().NoError(err)
			} else {
				suite.Require().Error(err)
			}

		})
	}
}

// TODO: unit and spec tags
func (suite *ConsumerTestSuite) TestOnChanOpenTry() {
	// OnOpenTry must error even with correct arguments
	consumerModule := consumer.NewAppModule(suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper)
	_, err := consumerModule.OnChanOpenTry(
		suite.ctx,
		channeltypes.ORDERED,
		[]string{"connection-1"},
		ccv.ConsumerPortID,
		"channel-1",
		nil,
		channeltypes.NewCounterparty(ccv.ProviderPortID, "channel-1"),
		ccv.Version,
	)
	suite.Require().Error(err, "OnChanOpenTry callback must error on consumer chain")
}

// TODO: unit and spec tags
// TestOnChanOpenAck tests the consumer module's OnChanOpenAck implementation against the spec:
// https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-ccf-coack1
func (suite *ConsumerTestSuite) TestOnChanOpenAck() {

	var (
		portID     string
		channelID  string
		metadataBz []byte
		metadata   providertypes.HandshakeMetadata
		err        error
	)
	testCases := []struct {
		name     string
		malleate func()
		expPass  bool
	}{
		{
			"success", func() {}, true,
		},
		{
			"invalid: provider channel already established",
			func() {
				suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.SetProviderChannel(suite.ctx, "channel-2")
			}, false,
		},
		{
			"invalid: cannot unmarshal ack metadata ",
			func() {
				metadataBz = []byte{78, 89, 20}
			}, false,
		},
		{
			"invalid: mismatched versions",
			func() {
				// Set counter party version to an invalid value, passed as marshaled metadata
				metadata.Version = "invalidVersion"
				metadataBz, err = (&metadata).Marshal()
				suite.Require().NoError(err)
			}, false,
		},
		// See ConsumerKeeper.GetConnectionHops as to why portID and channelID must be correct
		{
			"invalid: portID ",
			func() {
				portID = "invalidPort"
			}, false,
		},
		{
			"invalid: channelID ",
			func() {
				channelID = "invalidChan"
			}, false,
		},
	}

	for _, tc := range testCases {
		tc := tc
		suite.Run(fmt.Sprintf("Case: %s", tc.name), func() {
			suite.SetupTest() // reset
			portID = ccv.ConsumerPortID
			channelID = "channel-1"
			counterChannelID := "channel-2" // per spec this is not required by onChanOpenAck()
			suite.path.EndpointA.ChannelID = channelID

			// Set INIT channel on consumer chain
			suite.consumerChain.App.GetIBCKeeper().ChannelKeeper.SetChannel(
				suite.ctx,
				ccv.ConsumerPortID,
				channelID,
				channeltypes.NewChannel(
					channeltypes.INIT,
					channeltypes.ORDERED,
					channeltypes.NewCounterparty(ccv.ProviderPortID, ""),
					[]string{suite.path.EndpointA.ConnectionID},
					suite.path.EndpointA.ChannelConfig.Version,
				),
			)

			consumerModule := consumer.NewAppModule(
				suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper)

			metadata := providertypes.HandshakeMetadata{
				ProviderFeePoolAddr: "", // dummy address used
				Version:             suite.path.EndpointB.ChannelConfig.Version,
			}

			metadataBz, err = (&metadata).Marshal()
			suite.Require().NoError(err)

			tc.malleate() // Explicitly change fields already defined

			err = consumerModule.OnChanOpenAck(
				suite.ctx,
				portID,
				channelID,
				counterChannelID,
				string(metadataBz),
			)

			if tc.expPass {
				suite.Require().NoError(err)
			} else {
				suite.Require().Error(err)
			}
		})
	}
}

// TODO: unit and spec tags
func (suite *ConsumerTestSuite) TestOnChanOpenConfirm() {
	consumerModule := consumer.NewAppModule(suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper)
	err := consumerModule.OnChanOpenConfirm(suite.ctx, ccv.ConsumerPortID, "channel-1")
	suite.Require().Error(err, "OnChanOpenConfirm callback must error on consumer chain")
}

// TODO: unit and spec tags
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
				suite.consumerChain.App.GetIBCKeeper().ChannelKeeper.SetChannel(suite.ctx, ccv.ConsumerPortID, channelID,
					channeltypes.NewChannel(
						channeltypes.INIT, channeltypes.ORDERED, channeltypes.NewCounterparty(ccv.ProviderPortID, ""),
						[]string{suite.path.EndpointA.ConnectionID}, suite.path.EndpointA.ChannelConfig.Version),
				)
				suite.path.EndpointA.ChannelID = channelID
				suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.SetProviderChannel(suite.ctx, "different-channel")
			},
			expError: false,
		},
		{
			name: "can close duplicate open channel once provider channel is established",
			setup: func(suite *ConsumerTestSuite) {
				// create open channel
				suite.coordinator.CreateChannels(suite.path)
				suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.SetProviderChannel(suite.ctx, "different-channel")
			},
			expError: false,
		},
		{
			name: "cannot close in-progress channel, no established channel yet",
			setup: func(suite *ConsumerTestSuite) {
				// Set INIT channel on consumer chain
				suite.consumerChain.App.GetIBCKeeper().ChannelKeeper.SetChannel(suite.ctx, ccv.ConsumerPortID, channelID,
					channeltypes.NewChannel(
						channeltypes.INIT, channeltypes.ORDERED, channeltypes.NewCounterparty(ccv.ProviderPortID, ""),
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
				suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.SetProviderChannel(suite.ctx, suite.path.EndpointA.ChannelID)
			},
			expError: true,
		},
	}

	for _, tc := range testCases {
		tc := tc
		suite.Run(fmt.Sprintf("Case: %s", tc.name), func() {
			suite.SetupTest() // reset suite
			tc.setup(suite)

			consumerModule := consumer.NewAppModule(suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper)

			err := consumerModule.OnChanCloseInit(suite.ctx, ccv.ConsumerPortID, suite.path.EndpointA.ChannelID)

			if tc.expError {
				suite.Require().Error(err)
			} else {
				suite.Require().NoError(err)
			}
		})
	}
}

// TODO: Identify what other "close" IBC methods are missing from consumer or provider, and update testing table

// TODO: unit and spec tags
// TestVerifyProviderChain tests the VerifyProviderChain method for the consumer keeper
func (suite *ConsumerKeeperTestSuite) TestVerifyProviderChain() {
	var connectionHops []string
	channelID := "channel-0"
	testCases := []struct {
		name           string
		setup          func(suite *ConsumerKeeperTestSuite)
		connectionHops []string
		expError       bool
	}{
		{
			name: "success",
			setup: func(suite *ConsumerKeeperTestSuite) {
				// create consumer client on provider chain
				providerUnbondingPeriod := suite.providerChain.App.(*appProvider.App).GetStakingKeeper().UnbondingTime(suite.providerChain.GetContext())
				consumerUnbondingPeriod := utils.ComputeConsumerUnbondingPeriod(providerUnbondingPeriod)
				suite.CreateCustomClient(suite.path.EndpointB, consumerUnbondingPeriod)
				err := suite.path.EndpointB.CreateClient()
				suite.Require().NoError(err)

				suite.coordinator.CreateConnections(suite.path)

				// set connection hops to be connection hop from path endpoint
				connectionHops = []string{suite.path.EndpointA.ConnectionID}
			},
			connectionHops: []string{suite.path.EndpointA.ConnectionID},
			expError:       false,
		},
		{
			name: "connection hops is not length 1",
			setup: func(suite *ConsumerKeeperTestSuite) {
				// create consumer client on provider chain
				providerUnbondingPeriod := suite.providerChain.App.(*appProvider.App).GetStakingKeeper().UnbondingTime(suite.providerChain.GetContext())
				consumerUnbondingPeriod := utils.ComputeConsumerUnbondingPeriod(providerUnbondingPeriod)
				suite.CreateCustomClient(suite.path.EndpointB, consumerUnbondingPeriod)

				suite.coordinator.CreateConnections(suite.path)

				// set connection hops to be connection hop from path endpoint
				connectionHops = []string{suite.path.EndpointA.ConnectionID, "connection-2"}
			},
			expError: true,
		},
		{
			name: "connection does not exist",
			setup: func(suite *ConsumerKeeperTestSuite) {
				// set connection hops to be connection hop from path endpoint
				connectionHops = []string{"connection-dne"}
			},
			expError: true,
		},
		{
			name: "clientID does not match",
			setup: func(suite *ConsumerKeeperTestSuite) {
				// create consumer client on provider chain
				providerUnbondingPeriod := suite.providerChain.App.(*appProvider.App).GetStakingKeeper().UnbondingTime(suite.providerChain.GetContext())
				consumerUnbondingPeriod := utils.ComputeConsumerUnbondingPeriod(providerUnbondingPeriod)
				suite.CreateCustomClient(suite.path.EndpointB, consumerUnbondingPeriod)

				// create a new provider client on consumer chain that is different from the one in genesis
				suite.CreateCustomClient(suite.path.EndpointA, providerUnbondingPeriod)

				suite.coordinator.CreateConnections(suite.path)

				// set connection hops to be connection hop from path endpoint
				connectionHops = []string{suite.path.EndpointA.ConnectionID}
			},
			expError: true,
		},
	}

	for _, tc := range testCases {
		tc := tc
		suite.Run(fmt.Sprintf("Case: %s", tc.name), func() {
			suite.SetupTest() // reset suite

			tc.setup(suite)

			// Verify ProviderChain on consumer chain using path returned by setup
			err := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.VerifyProviderChain(suite.ctx, channelID, connectionHops)

			if tc.expError {
				suite.Require().Error(err, "invalid case did not return error")
			} else {
				suite.Require().NoError(err, "valid case returned error")
			}
		})
	}
}
