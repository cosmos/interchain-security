package e2e_test

import (
	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"

	app "github.com/cosmos/interchain-security/app/consumer"

	"fmt"

	ibctypes "github.com/cosmos/ibc-go/v3/modules/core/03-connection/types"
	clienttmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"

	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	providerkeeper "github.com/cosmos/interchain-security/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	tmtypes "github.com/tendermint/tendermint/types"

	"github.com/cosmos/interchain-security/x/ccv/utils"

	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	host "github.com/cosmos/ibc-go/v3/modules/core/24-host"

	"encoding/json"
	"time"

	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	"github.com/cosmos/interchain-security/x/ccv/consumer"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"

	abci "github.com/tendermint/tendermint/abci/types"
	crypto "github.com/tendermint/tendermint/proto/tendermint/crypto"

	sdk "github.com/cosmos/cosmos-sdk/types"
	distributiontypes "github.com/cosmos/cosmos-sdk/x/distribution/types"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"
	appProvider "github.com/cosmos/interchain-security/app/provider"
	"github.com/cosmos/interchain-security/x/ccv/provider"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
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
	valUpdates := tmtypes.TM2PB.ValidatorUpdates(suite.providerChain.Vals)

	restartGenesis := suite.consumerChain.App.(*app.App).ConsumerKeeper.ExportGenesis(suite.consumerChain.GetContext())
	suite.Require().Equal(valUpdates, restartGenesis.InitialValSet)

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

func (suite *ConsumerTestSuite) TestOnChanOpenConfirm() {
	consumerModule := consumer.NewAppModule(suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper)
	err := consumerModule.OnChanOpenConfirm(suite.ctx, ccv.ConsumerPortID, "channel-1")
	suite.Require().Error(err, "OnChanOpenConfirm callback must error on consumer chain")
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

// TestProviderClientMatches tests that the provider client managed by the consumer keeper matches the client keeper's client state
func (suite *ConsumerKeeperTestSuite) TestProviderClientMatches() {
	providerClientID, ok := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetProviderClientID(suite.ctx)
	suite.Require().True(ok)

	clientState, _ := suite.consumerChain.App.GetIBCKeeper().ClientKeeper.GetClientState(suite.ctx, providerClientID)
	suite.Require().Equal(suite.providerClient, clientState, "stored client state does not match genesis provider client")
}

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

// TestOnChanOpenTry validates the provider's OnChanOpenTry implementation against the spec:
// https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-cotry1
func (suite *ProviderTestSuite) TestOnChanOpenTry() {
	var (
		channel             *channeltypes.Channel
		counterpartyVersion string
		providerKeeper      *providerkeeper.Keeper
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
			"invalid order", func() {
				channel.Ordering = channeltypes.UNORDERED
			}, false,
		},
		{
			"invalid port ID", func() {
				suite.path.EndpointA.ChannelConfig.PortID = ibctesting.MockPort
			}, false,
		},
		{
			"invalid counter party port ID", func() {
				channel.Counterparty.PortId = ibctesting.MockPort
			}, false,
		},
		{
			"invalid counter party version", func() {
				counterpartyVersion = "invalidVersion"
			}, false,
		},
		{
			"unexpected client ID mapped to chain ID", func() {
				providerKeeper.SetConsumerClientId(
					suite.providerCtx(),
					suite.path.EndpointA.Chain.ChainID,
					"invalidClientID",
				)
			}, false,
		},
		{
			"other CCV channel exists for this consumer chain", func() {
				providerKeeper.SetChainToChannel(
					suite.providerCtx(),
					suite.path.EndpointA.Chain.ChainID,
					"some existing channel ID",
				)
			}, false,
		},
	}

	for _, tc := range testCases {
		tc := tc

		suite.Run(tc.name, func() {
			suite.SetupTest() // reset

			suite.path.EndpointA.ChannelConfig.PortID = ccv.ProviderPortID
			suite.path.EndpointA.ChannelID = "providerChanID"
			suite.path.EndpointB.ChannelConfig.PortID = ccv.ConsumerPortID
			suite.path.EndpointB.ChannelID = "consumerChanID"
			suite.path.EndpointA.ConnectionID = "ConnID"
			suite.path.EndpointA.ClientID = "ClientID"
			suite.path.EndpointA.Chain.ChainID = "ChainID"

			counterparty := channeltypes.NewCounterparty(
				suite.path.EndpointB.ChannelConfig.PortID,
				suite.path.EndpointA.ChannelID,
			)
			counterpartyVersion = ccv.Version

			channel = &channeltypes.Channel{
				State:          channeltypes.INIT,
				Ordering:       channeltypes.ORDERED,
				Counterparty:   counterparty,
				ConnectionHops: []string{suite.path.EndpointA.ConnectionID},
				Version:        counterpartyVersion,
			}

			providerKeeper = &suite.providerChain.App.(*appProvider.App).ProviderKeeper
			providerModule := provider.NewAppModule(providerKeeper)
			chanCap, err := suite.providerChain.App.GetScopedIBCKeeper().NewCapability(
				suite.providerCtx(),
				host.ChannelCapabilityPath(
					suite.path.EndpointA.ChannelConfig.PortID,
					suite.path.EndpointA.ChannelID,
				),
			)
			suite.Require().NoError(err)

			// Manual keeper setup
			connKeeper := suite.providerChain.App.GetIBCKeeper().ConnectionKeeper
			connKeeper.SetConnection(
				suite.providerCtx(),
				suite.path.EndpointA.ConnectionID,
				ibctypes.ConnectionEnd{
					ClientId: suite.path.EndpointA.ClientID,
				},
			)
			clientKeeper := suite.providerChain.App.GetIBCKeeper().ClientKeeper
			clientKeeper.SetClientState(
				suite.providerCtx(),
				suite.path.EndpointA.ClientID,
				&clienttmtypes.ClientState{
					ChainId: suite.path.EndpointA.Chain.ChainID,
				},
			)
			providerKeeper.SetConsumerClientId(
				suite.providerCtx(),
				suite.path.EndpointA.Chain.ChainID,
				suite.path.EndpointA.ClientID,
			)

			tc.malleate() // explicitly change fields

			metadata, err := providerModule.OnChanOpenTry(
				suite.providerCtx(),
				channel.Ordering,
				channel.GetConnectionHops(),
				suite.path.EndpointA.ChannelConfig.PortID,
				suite.path.EndpointA.ChannelID,
				chanCap,
				channel.Counterparty,
				counterpartyVersion,
			)

			if tc.expPass {
				suite.Require().NoError(err)
				md := &providertypes.HandshakeMetadata{}
				err = md.Unmarshal([]byte(metadata))
				suite.Require().NoError(err)
			} else {
				suite.Require().Error(err)
			}
		})
	}
}

func (suite *ProviderTestSuite) TestOnChanOpenInit() {
	// OnChanOpenInit must error for provider even with correct arguments
	providerModule := provider.NewAppModule(&suite.providerChain.App.(*appProvider.App).ProviderKeeper)

	err := providerModule.OnChanOpenInit(
		suite.providerCtx(),
		channeltypes.ORDERED,
		[]string{"connection-1"},
		ccv.ProviderPortID,
		"channel-1",
		nil,
		channeltypes.NewCounterparty(ccv.ConsumerPortID, "channel-1"),
		ccv.Version,
	)
	suite.Require().Error(err, "OnChanOpenInit must error on provider chain")
}

// TestConsumerChainProposalHandler tests the highest level handler
// for both ConsumerAdditionProposals and ConsumerRemovalProposals
//
// TODO: Determine if it's possible to make this a unit test
func (suite *ProviderTestSuite) TestConsumerChainProposalHandler() {
	var (
		ctx     sdk.Context
		content govtypes.Content
		err     error
	)

	testCases := []struct {
		name     string
		malleate func(*ProviderTestSuite)
		expPass  bool
	}{
		{
			"valid consumer addition proposal", func(suite *ProviderTestSuite) {
				initialHeight := clienttypes.NewHeight(2, 3)
				// ctx blocktime is after proposal's spawn time
				ctx = suite.providerChain.GetContext().WithBlockTime(time.Now().Add(time.Hour))
				content = types.NewConsumerAdditionProposal("title", "description", "chainID", initialHeight, []byte("gen_hash"), []byte("bin_hash"), time.Now())
			}, true,
		},
		{
			"valid consumer removal proposal", func(suite *ProviderTestSuite) {
				ctx = suite.providerChain.GetContext().WithBlockTime(time.Now().Add(time.Hour))
				content = types.NewConsumerRemovalProposal("title", "description", "chainID", time.Now())
			}, true,
		},
		{
			"nil proposal", func(suite *ProviderTestSuite) {
				ctx = suite.providerChain.GetContext()
				content = nil
			}, false,
		},
		{
			"unsupported proposal type", func(suite *ProviderTestSuite) {
				ctx = suite.providerChain.GetContext()
				content = distributiontypes.NewCommunityPoolSpendProposal(ibctesting.Title, ibctesting.Description, suite.providerChain.SenderAccount.GetAddress(), sdk.NewCoins(sdk.NewCoin("communityfunds", sdk.NewInt(10))))
			}, false,
		},
	}

	for _, tc := range testCases {
		tc := tc

		suite.Run(tc.name, func() {
			suite.SetupTest() // reset

			tc.malleate(suite)

			proposalHandler := provider.NewConsumerChainProposalHandler(suite.providerChain.App.(*appProvider.App).ProviderKeeper)

			err = proposalHandler(ctx, content)

			if tc.expPass {
				suite.Require().NoError(err)
			} else {
				suite.Require().Error(err)
			}
		})
	}
}

func (suite *ProviderKeeperTestSuite) TestMakeConsumerGenesis() {
	suite.SetupTest()

	actualGenesis, err := suite.providerChain.App.(*appProvider.App).ProviderKeeper.MakeConsumerGenesis(suite.providerChain.GetContext())
	suite.Require().NoError(err)

	jsonString := `{"params":{"enabled":true, "blocks_per_distribution_transmission":1000, "lock_unbonding_on_timeout": false},"new_chain":true,"provider_client_state":{"chain_id":"testchain1","trust_level":{"numerator":1,"denominator":3},"trusting_period":907200000000000,"unbonding_period":1814400000000000,"max_clock_drift":10000000000,"frozen_height":{},"latest_height":{"revision_height":5},"proof_specs":[{"leaf_spec":{"hash":1,"prehash_value":1,"length":1,"prefix":"AA=="},"inner_spec":{"child_order":[0,1],"child_size":33,"min_prefix_length":4,"max_prefix_length":12,"hash":1}},{"leaf_spec":{"hash":1,"prehash_value":1,"length":1,"prefix":"AA=="},"inner_spec":{"child_order":[0,1],"child_size":32,"min_prefix_length":1,"max_prefix_length":1,"hash":1}}],"upgrade_path":["upgrade","upgradedIBCState"],"allow_update_after_expiry":true,"allow_update_after_misbehaviour":true},"provider_consensus_state":{"timestamp":"2020-01-02T00:00:10Z","root":{"hash":"LpGpeyQVLUo9HpdsgJr12NP2eCICspcULiWa5u9udOA="},"next_validators_hash":"E30CE736441FB9101FADDAF7E578ABBE6DFDB67207112350A9A904D554E1F5BE"},"unbonding_sequences":null,"initial_val_set":[{"pub_key":{"type":"tendermint/PubKeyEd25519","value":"dcASx5/LIKZqagJWN0frOlFtcvz91frYmj/zmoZRWro="},"power":1}]}`

	var expectedGenesis consumertypes.GenesisState
	err = json.Unmarshal([]byte(jsonString), &expectedGenesis)
	suite.Require().NoError(err)

	// Zero out differing fields- TODO: figure out how to get the test suite to
	// keep these deterministic
	actualGenesis.ProviderConsensusState.NextValidatorsHash = []byte{}
	expectedGenesis.ProviderConsensusState.NextValidatorsHash = []byte{}

	// set valset to one empty validator because SetupTest() creates 4 validators per chain
	actualGenesis.InitialValSet = []abci.ValidatorUpdate{{PubKey: crypto.PublicKey{}, Power: actualGenesis.InitialValSet[0].Power}}
	expectedGenesis.InitialValSet[0].PubKey = crypto.PublicKey{}

	actualGenesis.ProviderConsensusState.Root.Hash = []byte{}
	expectedGenesis.ProviderConsensusState.Root.Hash = []byte{}

	suite.Require().Equal(actualGenesis, expectedGenesis, "consumer chain genesis created incorrectly")
}

func (suite *ProviderKeeperTestSuite) TestHandleConsumerAdditionProposal() {
	var (
		ctx      sdk.Context
		proposal *types.ConsumerAdditionProposal
		ok       bool
	)

	chainID := "chainID"
	initialHeight := clienttypes.NewHeight(2, 3)
	lockUbdOnTimeout := false

	testCases := []struct {
		name         string
		malleate     func(*ProviderKeeperTestSuite)
		expPass      bool
		spawnReached bool
	}{
		{
			"valid consumer addition proposal: spawn time reached", func(suite *ProviderKeeperTestSuite) {
				// ctx blocktime is after proposal's spawn time
				ctx = suite.providerChain.GetContext().WithBlockTime(time.Now().Add(time.Hour))
				content := types.NewConsumerAdditionProposal("title", "description", chainID, initialHeight, []byte("gen_hash"), []byte("bin_hash"), time.Now())
				proposal, ok = content.(*types.ConsumerAdditionProposal)
				suite.Require().True(ok)
				proposal.LockUnbondingOnTimeout = lockUbdOnTimeout
			}, true, true,
		},
		{
			"valid proposal: spawn time has not yet been reached", func(suite *ProviderKeeperTestSuite) {
				// ctx blocktime is before proposal's spawn time
				ctx = suite.providerChain.GetContext().WithBlockTime(time.Now())
				content := types.NewConsumerAdditionProposal("title", "description", chainID, initialHeight, []byte("gen_hash"), []byte("bin_hash"), time.Now().Add(time.Hour))
				proposal, ok = content.(*types.ConsumerAdditionProposal)
				suite.Require().True(ok)
				proposal.LockUnbondingOnTimeout = lockUbdOnTimeout
			}, true, false,
		},
	}

	for _, tc := range testCases {
		tc := tc

		suite.Run(tc.name, func() {
			suite.SetupTest()

			tc.malleate(suite)

			err := suite.providerChain.App.(*appProvider.App).ProviderKeeper.HandleConsumerAdditionProposal(ctx, proposal)
			if tc.expPass {
				suite.Require().NoError(err, "error returned on valid case")
				if tc.spawnReached {
					clientId, found := suite.providerChain.App.(*appProvider.App).ProviderKeeper.GetConsumerClientId(ctx, chainID)
					suite.Require().True(found, "consumer client not found")
					consumerGenesis, ok := suite.providerChain.App.(*appProvider.App).ProviderKeeper.GetConsumerGenesis(ctx, chainID)
					suite.Require().True(ok)

					expectedGenesis, err := suite.providerChain.App.(*appProvider.App).ProviderKeeper.MakeConsumerGenesis(ctx)
					suite.Require().NoError(err)

					suite.Require().Equal(expectedGenesis, consumerGenesis)
					suite.Require().NotEqual("", clientId, "consumer client was not created after spawn time reached")
				} else {
					gotProposal := suite.providerChain.App.(*appProvider.App).ProviderKeeper.GetPendingConsumerAdditionProp(ctx, proposal.SpawnTime, chainID)
					suite.Require().Equal(initialHeight, gotProposal.InitialHeight, "unexpected pending proposal (InitialHeight)")
					suite.Require().Equal(lockUbdOnTimeout, gotProposal.LockUnbondingOnTimeout, "unexpected pending proposal (LockUnbondingOnTimeout)")
				}
			} else {
				suite.Require().Error(err, "did not return error on invalid case")
			}
		})
	}
}
