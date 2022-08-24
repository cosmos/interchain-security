package e2e_test

import (
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"

	"bytes"
	"testing"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/x/ccv/utils"

	transfertypes "github.com/cosmos/ibc-go/v3/modules/apps/transfer/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"

	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	appProvider "github.com/cosmos/interchain-security/app/provider"
	"github.com/cosmos/interchain-security/testutil/simapp"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	"github.com/cosmos/interchain-security/x/ccv/types"

	tmtypes "github.com/tendermint/tendermint/types"

	"github.com/stretchr/testify/suite"
)

type ProviderTestSuite struct {
	suite.Suite

	coordinator *ibctesting.Coordinator

	// testing chains
	providerChain *ibctesting.TestChain
	consumerChain *ibctesting.TestChain

	path         *ibctesting.Path
	transferPath *ibctesting.Path
}

func (suite *ProviderTestSuite) SetupTest() {
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
		suite.providerCtx(),
		suite.consumerChain.ChainID,
		suite.consumerChain.LastHeader.GetHeight().(clienttypes.Height),
		false,
	)
	suite.Require().NoError(err)
	// move provider to next block to commit the state
	suite.providerChain.NextBlock()

	// initialize the consumer chain with the genesis state stored on the provider
	consumerGenesis, found := suite.providerChain.App.(*appProvider.App).ProviderKeeper.GetConsumerGenesis(
		suite.providerCtx(),
		suite.consumerChain.ChainID,
	)
	suite.Require().True(found, "consumer genesis not found")
	suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.InitGenesis(suite.consumerChain.GetContext(), &consumerGenesis)

	// create path for the CCV channel
	suite.path = ibctesting.NewPath(suite.consumerChain, suite.providerChain)

	// update CCV path with correct info
	// - set provider endpoint's clientID
	consumerClient, found := suite.providerChain.App.(*appProvider.App).ProviderKeeper.GetConsumerClientId(
		suite.providerCtx(),
		suite.consumerChain.ChainID,
	)
	suite.Require().True(found, "consumer client not found")
	suite.path.EndpointB.ClientID = consumerClient
	// - set consumer endpoint's clientID
	providerClient, found := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetProviderClientID(suite.consumerChain.GetContext())
	suite.Require().True(found, "provider client not found")
	suite.path.EndpointA.ClientID = providerClient
	// - client config
	providerUnbondingPeriod := suite.providerChain.App.(*appProvider.App).GetStakingKeeper().UnbondingTime(suite.providerCtx())
	suite.path.EndpointB.ClientConfig.(*ibctesting.TendermintConfig).UnbondingPeriod = providerUnbondingPeriod
	suite.path.EndpointB.ClientConfig.(*ibctesting.TendermintConfig).TrustingPeriod = providerUnbondingPeriod / utils.TrustingPeriodFraction
	consumerUnbondingPeriod := utils.ComputeConsumerUnbondingPeriod(providerUnbondingPeriod)
	suite.path.EndpointA.ClientConfig.(*ibctesting.TendermintConfig).UnbondingPeriod = consumerUnbondingPeriod
	suite.path.EndpointA.ClientConfig.(*ibctesting.TendermintConfig).TrustingPeriod = consumerUnbondingPeriod / utils.TrustingPeriodFraction
	// - channel config
	suite.path.EndpointA.ChannelConfig.PortID = consumertypes.PortID
	suite.path.EndpointB.ChannelConfig.PortID = providertypes.PortID
	suite.path.EndpointA.ChannelConfig.Version = types.Version
	suite.path.EndpointB.ChannelConfig.Version = types.Version
	suite.path.EndpointA.ChannelConfig.Order = channeltypes.ORDERED
	suite.path.EndpointB.ChannelConfig.Order = channeltypes.ORDERED

	// set chains sender account number
	// TODO: to be fixed in #151
	err = suite.path.EndpointB.Chain.SenderAccount.SetAccountNumber(6)
	suite.Require().NoError(err)
	err = suite.path.EndpointA.Chain.SenderAccount.SetAccountNumber(1)
	suite.Require().NoError(err)

	// create path for the transfer channel
	suite.transferPath = ibctesting.NewPath(suite.consumerChain, suite.providerChain)
	suite.transferPath.EndpointA.ChannelConfig.PortID = transfertypes.PortID
	suite.transferPath.EndpointB.ChannelConfig.PortID = transfertypes.PortID
	suite.transferPath.EndpointA.ChannelConfig.Version = transfertypes.Version
	suite.transferPath.EndpointB.ChannelConfig.Version = transfertypes.Version
}

func (suite *ProviderTestSuite) SetupCCVChannel() {
	suite.StartSetupCCVChannel()
	suite.CompleteSetupCCVChannel()
	suite.SetupTransferChannel()
}

func (suite *ProviderTestSuite) StartSetupCCVChannel() {
	suite.coordinator.CreateConnections(suite.path)

	err := suite.path.EndpointA.ChanOpenInit()
	suite.Require().NoError(err)

	err = suite.path.EndpointB.ChanOpenTry()
	suite.Require().NoError(err)
}

func (suite *ProviderTestSuite) CompleteSetupCCVChannel() {
	err := suite.path.EndpointA.ChanOpenAck()
	suite.Require().NoError(err)

	err = suite.path.EndpointB.ChanOpenConfirm()
	suite.Require().NoError(err)

	// ensure counterparty is up to date
	err = suite.path.EndpointA.UpdateClient()
	suite.Require().NoError(err)
}

func (suite *ProviderTestSuite) SetupTransferChannel() {
	// transfer path will use the same connection as ccv path

	suite.transferPath.EndpointA.ClientID = suite.path.EndpointA.ClientID
	suite.transferPath.EndpointA.ConnectionID = suite.path.EndpointA.ConnectionID
	suite.transferPath.EndpointB.ClientID = suite.path.EndpointB.ClientID
	suite.transferPath.EndpointB.ConnectionID = suite.path.EndpointB.ConnectionID

	// CCV channel handshake will automatically initiate transfer channel handshake on ACK
	// so transfer channel will be on stage INIT when CompleteSetupCCVChannel returns.
	suite.transferPath.EndpointA.ChannelID = suite.consumerChain.App.(*appConsumer.App).
		ConsumerKeeper.GetDistributionTransmissionChannel(suite.consumerChain.GetContext())

	// Complete TRY, ACK, CONFIRM for transfer path
	err := suite.transferPath.EndpointB.ChanOpenTry()
	suite.Require().NoError(err)

	err = suite.transferPath.EndpointA.ChanOpenAck()
	suite.Require().NoError(err)

	err = suite.transferPath.EndpointB.ChanOpenConfirm()
	suite.Require().NoError(err)

	// ensure counterparty is up to date
	err = suite.transferPath.EndpointA.UpdateClient()
	suite.Require().NoError(err)
}

// TODO: Can this be consolidated with ProviderTestSuite above?
type ProviderKeeperTestSuite struct {
	suite.Suite
	coordinator *ibctesting.Coordinator

	// testing chains
	providerChain *ibctesting.TestChain
	consumerChain *ibctesting.TestChain
	path          *ibctesting.Path
	ctx           sdk.Context
}

func (suite *ProviderKeeperTestSuite) SetupTest() {
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
	providerClient, found := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetProviderClientID(suite.consumerChain.GetContext())
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
	suite.path.EndpointA.ChannelConfig.Version = types.Version
	suite.path.EndpointB.ChannelConfig.Version = types.Version
	suite.path.EndpointA.ChannelConfig.Order = channeltypes.ORDERED
	suite.path.EndpointB.ChannelConfig.Order = channeltypes.ORDERED

	// set chains sender account number
	// TODO: to be fixed in #151
	err = suite.path.EndpointB.Chain.SenderAccount.SetAccountNumber(6)
	suite.Require().NoError(err)
	err = suite.path.EndpointA.Chain.SenderAccount.SetAccountNumber(1)
	suite.Require().NoError(err)

	suite.ctx = suite.providerChain.GetContext()
}

func TestProviderKeeperTestSuite(t *testing.T) {
	suite.Run(t, new(ProviderKeeperTestSuite))
}

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
	providerClient, found := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetProviderClientID(suite.consumerChain.GetContext())
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

// TODO: Can this be consolidated with above?
type ConsumerKeeperTestSuite struct {
	suite.Suite

	coordinator *ibctesting.Coordinator

	// testing chains
	providerChain *ibctesting.TestChain
	consumerChain *ibctesting.TestChain

	providerClient    *ibctmtypes.ClientState
	providerConsState *ibctmtypes.ConsensusState

	path *ibctesting.Path

	ctx sdk.Context
}

func (suite *ConsumerKeeperTestSuite) SetupTest() {
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
	suite.providerClient = consumerGenesis.ProviderClientState
	suite.providerConsState = consumerGenesis.ProviderConsensusState

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
	providerClient, found := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetProviderClientID(suite.consumerChain.GetContext())
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
}

func (suite *ConsumerKeeperTestSuite) SetupCCVChannel() {
	suite.coordinator.CreateConnections(suite.path)
	suite.coordinator.CreateChannels(suite.path)
}

func TestConsumerKeeperTestSuite(t *testing.T) {
	suite.Run(t, new(ConsumerKeeperTestSuite))
}
