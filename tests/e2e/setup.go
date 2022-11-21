package e2e

import (
	"bytes"
	"testing"

	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	e2eutil "github.com/cosmos/interchain-security/testutil/e2e"

	icstestingutils "github.com/cosmos/interchain-security/testutil/ibc_testing"
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
	setupCallback SetupCallback

	providerChain *ibctesting.TestChain
	providerApp   e2eutil.ProviderApp

	// The first consumer chain among multiple.
	consumerChain *ibctesting.TestChain
	// The first consumer app among multiple.
	consumerApp e2eutil.ConsumerApp
	// The ccv path to the first consumer among multiple.
	path *ibctesting.Path
	// The transfer path to the first consumer among multiple.
	transferPath *ibctesting.Path

	// A map from consumer chain ID to its consumer bundle.
	// The preferred way to access chains, apps, and paths when designing tests around multiple consumers.
	consumerBundles map[string]*icstestingutils.ConsumerBundle
	skippedTests    map[string]bool
}

// NewCCVTestSuite returns a new instance of CCVTestSuite, ready to be tested against using suite.Run().
func NewCCVTestSuite[Tp e2eutil.ProviderApp, Tc e2eutil.ConsumerApp](
	providerAppIniter ibctesting.AppIniter, consumerAppIniter ibctesting.AppIniter, skippedTests []string) *CCVTestSuite {

	ccvSuite := new(CCVTestSuite)

	// Define callback called before each test.
	ccvSuite.setupCallback = func(t *testing.T) (
		*ibctesting.Coordinator,
		*ibctesting.TestChain,
		e2eutil.ProviderApp,
		map[string]*icstestingutils.ConsumerBundle,
	) {
		// Instantiate the test coordinator.
		coordinator := ibctesting.NewCoordinator(t, 0)

		// Add provider to coordinator, store returned test chain and app.
		// Concrete provider app type is passed to the generic function here.
		provider, providerApp := icstestingutils.AddProvider[Tp](
			coordinator, t, providerAppIniter)

		numConsumers := 5

		// Add specified number of consumers to coordinator, store returned test chains and apps.
		// Concrete consumer app type is passed to the generic function here.
		consumerBundles := icstestingutils.AddConsumers[Tc](
			coordinator, t, numConsumers, consumerAppIniter)

		// Pass variables to suite.
		return coordinator, provider, providerApp, consumerBundles
	}

	ccvSuite.skippedTests = make(map[string]bool)
	for _, testName := range skippedTests {
		ccvSuite.skippedTests[testName] = true
	}
	return ccvSuite
}

// Callback for instantiating a new coordinator, provider/consumer test chains, and provider/consumer apps
// before every test defined on the suite.
type SetupCallback func(t *testing.T) (
	coord *ibctesting.Coordinator,
	providerChain *ibctesting.TestChain,
	providerApp e2eutil.ProviderApp,
	consumerBundles map[string]*icstestingutils.ConsumerBundle,
)

func (suite *CCVTestSuite) BeforeTest(suiteName, testName string) {
	if suite.skippedTests[testName] {
		suite.T().Skip()
	}
}

// SetupTest sets up in-mem state before every test
func (suite *CCVTestSuite) SetupTest() {

	// Instantiate new test utils using callback
	suite.coordinator, suite.providerChain,
		suite.providerApp, suite.consumerBundles = suite.setupCallback(suite.T())

	// valsets must match between provider and all consumers
	for _, bundle := range suite.consumerBundles {

		providerValUpdates := tmtypes.TM2PB.ValidatorUpdates(suite.providerChain.Vals)
		consumerValUpdates := tmtypes.TM2PB.ValidatorUpdates(bundle.Chain.Vals)
		suite.Require().True(len(providerValUpdates) == len(consumerValUpdates), "initial valset not matching")
		for i := 0; i < len(providerValUpdates); i++ {
			addr1 := utils.GetChangePubKeyAddress(providerValUpdates[i])
			addr2 := utils.GetChangePubKeyAddress(consumerValUpdates[i])
			suite.Require().True(bytes.Equal(addr1, addr2), "validator mismatch")
		}
		// Move each consumer to next block
		bundle.Chain.NextBlock()
	}

	// move provider to next block
	suite.providerChain.NextBlock()

	providerKeeper := suite.providerApp.GetProviderKeeper()

	for chainID, bundle := range suite.consumerBundles {
		// For each consumer, create client to that consumer on the provider chain.
		err := providerKeeper.CreateConsumerClient(
			suite.providerCtx(),
			chainID,
			bundle.Chain.LastHeader.GetHeight().(clienttypes.Height),
			false,
		)
		suite.Require().NoError(err)
	}

	// move provider to next block to commit the state
	suite.providerChain.NextBlock()

	// initialize each consumer chain with it's corresponding genesis state
	// stored on the provider.
	for chainID, bundle := range suite.consumerBundles {

		consumerGenesisState, found := providerKeeper.GetConsumerGenesis(
			suite.providerCtx(),
			chainID,
		)
		suite.Require().True(found, "consumer genesis not found")

		consumerKeeper := bundle.GetKeeper()
		consumerKeeper.InitGenesis(bundle.GetCtx(), &consumerGenesisState)

		// Confirm client and cons state for consumer were set correctly in InitGenesis
		consumerEndpointClientState,
			consumerEndpointConsState := suite.GetConsumerEndpointClientAndConsState(*bundle)
		suite.Require().Equal(consumerGenesisState.ProviderClientState, consumerEndpointClientState)
		suite.Require().Equal(consumerGenesisState.ProviderConsensusState, consumerEndpointConsState)

		// create path for the CCV channel
		bundle.Path = ibctesting.NewPath(bundle.Chain, suite.providerChain)

		// Set provider endpoint's clientID for each consumer
		providerEndpointClientID, found := providerKeeper.GetConsumerClientId(
			suite.providerCtx(),
			chainID,
		)
		suite.Require().True(found, "provider endpoint clientID not found")
		bundle.Path.EndpointB.ClientID = providerEndpointClientID

		// Set consumer endpoint's clientID
		consumerKeeper = bundle.GetKeeper()
		consumerEndpointClientID, found := consumerKeeper.GetProviderClientID(bundle.GetCtx())
		suite.Require().True(found, "consumer endpoint clientID not found")
		bundle.Path.EndpointA.ClientID = consumerEndpointClientID

		// Note: suite.path.EndpointA.ClientConfig and suite.path.EndpointB.ClientConfig are not populated,
		// since these IBC testing package fields are unused in our tests.

		// Confirm client config is now correct
		suite.ValidateEndpointsClientConfig(*bundle)

		// - channel config
		bundle.Path.EndpointA.ChannelConfig.PortID = ccv.ConsumerPortID
		bundle.Path.EndpointB.ChannelConfig.PortID = ccv.ProviderPortID
		bundle.Path.EndpointA.ChannelConfig.Version = ccv.Version
		bundle.Path.EndpointB.ChannelConfig.Version = ccv.Version
		bundle.Path.EndpointA.ChannelConfig.Order = channeltypes.ORDERED
		bundle.Path.EndpointB.ChannelConfig.Order = channeltypes.ORDERED

		// create path for the transfer channel
		bundle.TransferPath = ibctesting.NewPath(bundle.Chain, suite.providerChain)
		bundle.TransferPath.EndpointA.ChannelConfig.PortID = transfertypes.PortID
		bundle.TransferPath.EndpointB.ChannelConfig.PortID = transfertypes.PortID
		bundle.TransferPath.EndpointA.ChannelConfig.Version = transfertypes.Version
		bundle.TransferPath.EndpointB.ChannelConfig.Version = transfertypes.Version
	}

	// Support tests that were written before multiple consumers were supported.
	firstBundle := suite.getFirstBundle()
	suite.consumerApp = firstBundle.App
	suite.consumerChain = firstBundle.Chain
	suite.path = firstBundle.Path
	suite.transferPath = firstBundle.TransferPath
}

func (suite *CCVTestSuite) SetupAllCCVChannels() {
	for _, bundle := range suite.consumerBundles {
		suite.SetupCCVChannel(bundle.Path)
	}
}

func (suite *CCVTestSuite) SetupCCVChannel(path *ibctesting.Path) {
	suite.StartSetupCCVChannel(path)
	suite.CompleteSetupCCVChannel(path)
}

func (suite *CCVTestSuite) StartSetupCCVChannel(path *ibctesting.Path) {
	suite.coordinator.CreateConnections(path)

	err := path.EndpointA.ChanOpenInit()
	suite.Require().NoError(err)

	err = path.EndpointB.ChanOpenTry()
	suite.Require().NoError(err)
}

func (suite *CCVTestSuite) CompleteSetupCCVChannel(path *ibctesting.Path) {
	err := path.EndpointA.ChanOpenAck()
	suite.Require().NoError(err)

	err = path.EndpointB.ChanOpenConfirm()
	suite.Require().NoError(err)

	// ensure counterparty is up to date
	err = path.EndpointA.UpdateClient()
	suite.Require().NoError(err)
}

// TODO: Make SetupTransferChannel functional for multiple consumers by pattern matching SetupCCVChannel.
// See: https://github.com/cosmos/interchain-security/issues/506
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

func (s CCVTestSuite) ValidateEndpointsClientConfig(consumerBundle icstestingutils.ConsumerBundle) {
	consumerKeeper := consumerBundle.GetKeeper()
	providerStakingKeeper := s.providerApp.GetStakingKeeper()

	consumerUnbondingPeriod := consumerKeeper.GetUnbondingPeriod(consumerBundle.GetCtx())
	cs, ok := s.providerApp.GetIBCKeeper().ClientKeeper.GetClientState(s.providerCtx(),
		consumerBundle.Path.EndpointB.ClientID)
	s.Require().True(ok)
	s.Require().Equal(
		consumerUnbondingPeriod,
		cs.(*ibctmtypes.ClientState).UnbondingPeriod,
		"unexpected unbonding period in consumer client state",
	)

	providerUnbondingPeriod := providerStakingKeeper.UnbondingTime(s.providerCtx())
	cs, ok = consumerBundle.App.GetIBCKeeper().ClientKeeper.GetClientState(
		consumerBundle.GetCtx(), consumerBundle.Path.EndpointA.ClientID)
	s.Require().True(ok)
	s.Require().Equal(
		providerUnbondingPeriod,
		cs.(*ibctmtypes.ClientState).UnbondingPeriod,
		"unexpected unbonding period in provider client state",
	)
}
