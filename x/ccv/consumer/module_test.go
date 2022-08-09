package consumer_test

import (
	"bytes"
	"fmt"
	"testing"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"

	"github.com/cosmos/ibc-go/modules/core/exported"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	commitmenttypes "github.com/cosmos/ibc-go/v3/modules/core/23-commitment/types"
	host "github.com/cosmos/ibc-go/v3/modules/core/24-host"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"

	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	appProvider "github.com/cosmos/interchain-security/app/provider"
	"github.com/cosmos/interchain-security/testutil/simapp"
	"github.com/cosmos/interchain-security/x/ccv/consumer"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	"github.com/cosmos/interchain-security/x/ccv/utils"

	tmtypes "github.com/tendermint/tendermint/types"

	"github.com/stretchr/testify/require"
	"github.com/stretchr/testify/suite"
)

type ConsumerTestSuite struct {
	suite.Suite

	coordinator *ibctesting.Coordinator

	// testing chains
	providerChain *ibctesting.TestChain
	consumerChain *ibctesting.TestChain

	path *ibctesting.Path

	ctx sdk.Context
}

func (suite *ConsumerTestSuite) SetupTest() {
	suite.coordinator, suite.providerChain, suite.consumerChain = simapp.NewProviderConsumerCoordinator(suite.T())

	// valsets must match
	providerValUpdates := tmtypes.TM2PB.ValidatorUpdates(suite.providerChain.Vals)
	consumerValUpdates := tmtypes.TM2PB.ValidatorUpdates(suite.consumerChain.Vals)
	suite.Require().True(len(providerValUpdates) == len(consumerValUpdates), "initial valset not matching")
	for i := 0; i < len(providerValUpdates); i++ {
		addr1 := utils.GetChangePubKeyAddress(providerValUpdates[i])
		addr2 := utils.GetChangePubKeyAddress(consumerValUpdates[i])
		suite.Require().True(bytes.Equal(addr1, addr2), "validator mismatch")
	}

	// move both chains to the next block
	suite.providerChain.NextBlock()
	suite.consumerChain.NextBlock()

	// create consumer client on provider chain and set as consumer client for consumer chainID in provider keeper.
	err := suite.providerChain.App.(*appProvider.App).ProviderKeeper.CreateConsumerClient(
		suite.providerChain.GetContext(),
		suite.consumerChain.ChainID,
		suite.consumerChain.LastHeader.GetHeight().(clienttypes.Height),
		false,
	)
	suite.Require().NoError(err)
	// move provider to next block to commit the state
	suite.providerChain.NextBlock()

	// initialize the consumer chain with the genesis state stored on the provider
	consumerGenesis, found := suite.providerChain.App.(*appProvider.App).ProviderKeeper.GetConsumerGenesis(
		suite.providerChain.GetContext(),
		suite.consumerChain.ChainID,
	)
	suite.Require().True(found, "consumer genesis not found")
	suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.InitGenesis(suite.consumerChain.GetContext(), &consumerGenesis)

	// create path for the CCV channel
	suite.path = ibctesting.NewPath(suite.consumerChain, suite.providerChain)

	// update CCV path with correct info
	// - set provider endpoint's clientID
	consumerClient, found := suite.providerChain.App.(*appProvider.App).ProviderKeeper.GetConsumerClientId(
		suite.providerChain.GetContext(),
		suite.consumerChain.ChainID,
	)
	suite.Require().True(found, "consumer client not found")
	suite.path.EndpointB.ClientID = consumerClient
	// - set consumer endpoint's clientID
	providerClient, found := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetProviderClient(suite.consumerChain.GetContext())
	suite.Require().True(found, "provider client not found")
	suite.path.EndpointA.ClientID = providerClient
	// - client config
	providerUnbondingPeriod := suite.providerChain.App.(*appProvider.App).GetStakingKeeper().UnbondingTime(suite.providerChain.GetContext())
	suite.path.EndpointB.ClientConfig.(*ibctesting.TendermintConfig).UnbondingPeriod = providerUnbondingPeriod
	suite.path.EndpointB.ClientConfig.(*ibctesting.TendermintConfig).TrustingPeriod = providerUnbondingPeriod / utils.TrustingPeriodFraction
	consumerUnbondingPeriod := utils.ComputeConsumerUnbondingPeriod(providerUnbondingPeriod)
	suite.path.EndpointA.ClientConfig.(*ibctesting.TendermintConfig).UnbondingPeriod = consumerUnbondingPeriod
	suite.path.EndpointA.ClientConfig.(*ibctesting.TendermintConfig).TrustingPeriod = consumerUnbondingPeriod / utils.TrustingPeriodFraction
	// - channel config
	suite.path.EndpointA.ChannelConfig.PortID = consumertypes.PortID
	suite.path.EndpointB.ChannelConfig.PortID = providertypes.PortID
	suite.path.EndpointA.ChannelConfig.Version = ccv.Version
	suite.path.EndpointB.ChannelConfig.Version = ccv.Version
	suite.path.EndpointA.ChannelConfig.Order = channeltypes.ORDERED
	suite.path.EndpointB.ChannelConfig.Order = channeltypes.ORDERED

	// set chains sender account number
	// TODO: to be fixed in #151
	err = suite.path.EndpointB.Chain.SenderAccount.SetAccountNumber(6)
	suite.Require().NoError(err)
	err = suite.path.EndpointA.Chain.SenderAccount.SetAccountNumber(1)
	suite.Require().NoError(err)

	suite.ctx = suite.consumerChain.GetContext()

	suite.coordinator.CreateConnections(suite.path)
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
				suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.SetProviderChannel(suite.ctx, "channel-2")
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
				// - client config
				providerUnbondingPeriod := suite.providerChain.App.(*appProvider.App).GetStakingKeeper().UnbondingTime(suite.providerChain.GetContext())
				path.EndpointB.ClientConfig.(*ibctesting.TendermintConfig).UnbondingPeriod = providerUnbondingPeriod
				path.EndpointB.ClientConfig.(*ibctesting.TendermintConfig).TrustingPeriod = providerUnbondingPeriod / utils.TrustingPeriodFraction
				consumerUnbondingPeriod := utils.ComputeConsumerUnbondingPeriod(providerUnbondingPeriod)
				path.EndpointA.ClientConfig.(*ibctesting.TendermintConfig).UnbondingPeriod = consumerUnbondingPeriod
				path.EndpointA.ClientConfig.(*ibctesting.TendermintConfig).TrustingPeriod = consumerUnbondingPeriod / utils.TrustingPeriodFraction
				// - channel config
				path.EndpointA.ChannelConfig.PortID = consumertypes.PortID
				path.EndpointB.ChannelConfig.PortID = providertypes.PortID
				path.EndpointA.ChannelConfig.Version = ccv.Version
				path.EndpointB.ChannelConfig.Version = ccv.Version
				path.EndpointA.ChannelConfig.Order = channeltypes.ORDERED
				path.EndpointB.ChannelConfig.Order = channeltypes.ORDERED

				// create consumer client on provider chain, and provider client on consumer chain
				err := suite.CreateCustomClient(path.EndpointB, consumerUnbondingPeriod)
				suite.Require().NoError(err)
				err = suite.CreateCustomClient(path.EndpointA, providerUnbondingPeriod)
				suite.Require().NoError(err)

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

			consumerModule := consumer.NewAppModule(suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper)
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

// CreateCustomClient creates an IBC client on the endpoint
// using the given unbonding period.
// It will update the clientID for the endpoint if the message
// is successfully executed.
func (suite *ConsumerTestSuite) CreateCustomClient(endpoint *ibctesting.Endpoint, unbondingPeriod time.Duration) (err error) {
	// ensure counterparty has committed state
	endpoint.Chain.Coordinator.CommitBlock(endpoint.Counterparty.Chain)

	suite.Require().Equal(exported.Tendermint, endpoint.ClientConfig.GetClientType(), "only Tendermint client supported")

	tmConfig, ok := endpoint.ClientConfig.(*ibctesting.TendermintConfig)
	require.True(endpoint.Chain.T, ok)
	tmConfig.UnbondingPeriod = unbondingPeriod
	tmConfig.TrustingPeriod = unbondingPeriod / utils.TrustingPeriodFraction

	height := endpoint.Counterparty.Chain.LastHeader.GetHeight().(clienttypes.Height)
	UpgradePath := []string{"upgrade", "upgradedIBCState"}
	clientState := ibctmtypes.NewClientState(
		endpoint.Counterparty.Chain.ChainID, tmConfig.TrustLevel, tmConfig.TrustingPeriod, tmConfig.UnbondingPeriod, tmConfig.MaxClockDrift,
		height, commitmenttypes.GetSDKSpecs(), UpgradePath, tmConfig.AllowUpdateAfterExpiry, tmConfig.AllowUpdateAfterMisbehaviour,
	)
	consensusState := endpoint.Counterparty.Chain.LastHeader.ConsensusState()

	msg, err := clienttypes.NewMsgCreateClient(
		clientState, consensusState, endpoint.Chain.SenderAccount.GetAddress().String(),
	)
	require.NoError(endpoint.Chain.T, err)

	res, err := endpoint.Chain.SendMsgs(msg)
	if err != nil {
		return err
	}

	endpoint.ClientID, err = ibctesting.ParseClientIDFromEvents(res.GetEvents())
	require.NoError(endpoint.Chain.T, err)

	return nil
}

func (suite *ConsumerTestSuite) TestOnChanOpenTry() {
	// OnOpenTry must error even with correct arguments
	consumerModule := consumer.NewAppModule(suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper)
	chanCap, err := suite.consumerChain.App.GetScopedIBCKeeper().NewCapability(suite.ctx, host.ChannelCapabilityPath(consumertypes.PortID, suite.path.EndpointA.ChannelID))
	suite.Require().NoError(err)

	_, err = consumerModule.OnChanOpenTry(suite.ctx, channeltypes.ORDERED, []string{"connection-1"}, consumertypes.PortID, "channel-1", chanCap, channeltypes.NewCounterparty(providertypes.PortID, "channel-1"), ccv.Version)
	suite.Require().Error(err, "OnChanOpenTry callback must error on consumer chain")
}

func (suite *ConsumerTestSuite) TestOnChanOpenAck() {
	channelID := "channel-1"
	counterChannelID := "channel-2"
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
				suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.SetProviderChannel(suite.ctx, "channel-2")
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

			consumerModule := consumer.NewAppModule(suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper)

			md := providertypes.HandshakeMetadata{
				ProviderFeePoolAddr: "", // dummy address used
				Version:             suite.path.EndpointB.ChannelConfig.Version,
			}
			mdBz, err := (&md).Marshal()
			suite.Require().NoError(err)

			err = consumerModule.OnChanOpenAck(suite.ctx, consumertypes.PortID, channelID, counterChannelID, string(mdBz))
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

	consumerModule := consumer.NewAppModule(suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper)

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
