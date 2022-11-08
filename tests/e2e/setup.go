package e2e

import (
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"

	"bytes"
	"testing"

	e2e "github.com/cosmos/interchain-security/testutil/e2e"

	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	"github.com/cosmos/interchain-security/x/ccv/utils"

	transfertypes "github.com/cosmos/ibc-go/v3/modules/apps/transfer/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"

	tmtypes "github.com/tendermint/tendermint/types"

	"github.com/stretchr/testify/suite"
)

// CCVTestSuite is an in-mem test suite which implements the standard group of tests validating
// the e2e functionality of ccv enabled chains.
// Any method implemented for this struct will be ran when suite.Run() is called.
type CCVTestSuite struct {
	suite.Suite
	coordinator   *ibctesting.Coordinator
	providerChain *ibctesting.TestChain
	consumerChain *ibctesting.TestChain
	providerApp   e2e.ProviderApp
	consumerApp   e2e.ConsumerApp
	path          *ibctesting.Path
	transferPath  *ibctesting.Path
	setupCallback SetupCallback
}

// NewCCVTestSuite returns a new instance of CCVTestSuite, ready to be tested against using suite.Run().
func NewCCVTestSuite(setupCallback SetupCallback) *CCVTestSuite {
	ccvSuite := new(CCVTestSuite)
	ccvSuite.setupCallback = setupCallback
	return ccvSuite
}

// Callback for instantiating a new coordinator, provider/consumer test chains, and provider/consumer app
// before every test defined on the suite.
type SetupCallback func(t *testing.T) (
	coord *ibctesting.Coordinator,
	providerChain *ibctesting.TestChain,
	consumerChain *ibctesting.TestChain,
	providerApp e2e.ProviderApp,
	consumerApp e2e.ConsumerApp,
)

// SetupTest sets up in-mem state before every test
func (suite *CCVTestSuite) SetupTest() {

	// Instantiate new test utils using callback
	suite.coordinator, suite.providerChain,
		suite.consumerChain, suite.providerApp,
		suite.consumerApp = suite.setupCallback(suite.T())

	providerKeeper := suite.providerApp.GetProviderKeeper()
	consumerKeeper := suite.consumerApp.GetConsumerKeeper()

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
	err := providerKeeper.CreateConsumerClient(
		suite.providerCtx(),
		suite.consumerChain.ChainID,
		suite.consumerChain.LastHeader.GetHeight().(clienttypes.Height),
		false,
	)
	suite.Require().NoError(err)
	// move provider to next block to commit the state
	suite.providerChain.NextBlock()

	// initialize the consumer chain with the genesis state stored on the provider
	consumerGenesisState, found := providerKeeper.GetConsumerGenesis(
		suite.providerCtx(),
		suite.consumerChain.ChainID,
	)
	suite.Require().True(found, "consumer genesis not found")
	consumerKeeper.InitGenesis(suite.consumerCtx(), &consumerGenesisState)

	// Confirm client and cons state for consumer were set correctly in InitGenesis
	consumerEndpointClientState, consumerEndpointConsState := suite.GetConsumerEndpointClientAndConsState()
	suite.Require().Equal(consumerGenesisState.ProviderClientState, consumerEndpointClientState)
	suite.Require().Equal(consumerGenesisState.ProviderConsensusState, consumerEndpointConsState)

	// create path for the CCV channel
	suite.path = ibctesting.NewPath(suite.consumerChain, suite.providerChain)

	// Set provider endpoint's clientID
	providerEndpointClientID, found := providerKeeper.GetConsumerClientId(
		suite.providerCtx(),
		suite.consumerChain.ChainID,
	)
	suite.Require().True(found, "provider endpoint clientID not found")
	suite.path.EndpointB.ClientID = providerEndpointClientID

	// Set consumer endpoint's clientID
	consumerEndpointClientID, found := consumerKeeper.GetProviderClientID(suite.consumerChain.GetContext())
	suite.Require().True(found, "consumer endpoint clientID not found")
	suite.path.EndpointA.ClientID = consumerEndpointClientID

	// Note: suite.path.EndpointA.ClientConfig and suite.path.EndpointB.ClientConfig are not populated,
	// since these IBC testing package fields are unused in our tests.

	// Confirm client config is now correct
	suite.ValidateEndpointsClientConfig()

	// - channel config
	suite.path.EndpointA.ChannelConfig.PortID = ccv.ConsumerPortID
	suite.path.EndpointB.ChannelConfig.PortID = ccv.ProviderPortID
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

	// create path for the transfer channel
	suite.transferPath = ibctesting.NewPath(suite.consumerChain, suite.providerChain)
	suite.transferPath.EndpointA.ChannelConfig.PortID = transfertypes.PortID
	suite.transferPath.EndpointB.ChannelConfig.PortID = transfertypes.PortID
	suite.transferPath.EndpointA.ChannelConfig.Version = transfertypes.Version
	suite.transferPath.EndpointB.ChannelConfig.Version = transfertypes.Version
}

func (suite *CCVTestSuite) SetupCCVChannel() {
	suite.StartSetupCCVChannel()
	suite.CompleteSetupCCVChannel()
}

func (suite *CCVTestSuite) StartSetupCCVChannel() {
	suite.coordinator.CreateConnections(suite.path)

	err := suite.path.EndpointA.ChanOpenInit()
	suite.Require().NoError(err)

	err = suite.path.EndpointB.ChanOpenTry()
	suite.Require().NoError(err)
}

func (suite *CCVTestSuite) CompleteSetupCCVChannel() {
	err := suite.path.EndpointA.ChanOpenAck()
	suite.Require().NoError(err)

	err = suite.path.EndpointB.ChanOpenConfirm()
	suite.Require().NoError(err)

	// ensure counterparty is up to date
	err = suite.path.EndpointA.UpdateClient()
	suite.Require().NoError(err)
}

func (suite *CCVTestSuite) SetupTransferChannel() {
	// transfer path will use the same connection as ccv path

	suite.transferPath.EndpointA.ClientID = suite.path.EndpointA.ClientID
	suite.transferPath.EndpointA.ConnectionID = suite.path.EndpointA.ConnectionID
	suite.transferPath.EndpointB.ClientID = suite.path.EndpointB.ClientID
	suite.transferPath.EndpointB.ConnectionID = suite.path.EndpointB.ConnectionID

	// CCV channel handshake will automatically initiate transfer channel handshake on ACK
	// so transfer channel will be on stage INIT when CompleteSetupCCVChannel returns.
	suite.transferPath.EndpointA.ChannelID =
		suite.consumerApp.GetConsumerKeeper().GetDistributionTransmissionChannel(
			suite.consumerChain.GetContext())

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

func (s CCVTestSuite) ValidateEndpointsClientConfig() {
	consumerKeeper := s.consumerApp.GetConsumerKeeper()
	providerStakingKeeper := s.providerApp.GetStakingKeeper()

	consumerUnbondingPeriod := consumerKeeper.GetUnbondingPeriod(s.consumerCtx())
	cs, ok := s.providerApp.GetIBCKeeper().ClientKeeper.GetClientState(s.providerCtx(), s.path.EndpointB.ClientID)
	s.Require().True(ok)
	s.Require().Equal(
		consumerUnbondingPeriod,
		cs.(*ibctmtypes.ClientState).UnbondingPeriod,
		"unexpected unbonding period in consumer client state",
	)

	providerUnbondingPeriod := providerStakingKeeper.UnbondingTime(s.providerCtx())
	cs, ok = s.consumerApp.GetIBCKeeper().ClientKeeper.GetClientState(s.consumerCtx(), s.path.EndpointA.ClientID)
	s.Require().True(ok)
	s.Require().Equal(
		providerUnbondingPeriod,
		cs.(*ibctmtypes.ClientState).UnbondingPeriod,
		"unexpected unbonding period in provider client state",
	)
}
