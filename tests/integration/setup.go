package integration

import (
	"context"
	"fmt"
	"testing"

	transfertypes "github.com/cosmos/ibc-go/v10/modules/apps/transfer/types"
	channeltypes "github.com/cosmos/ibc-go/v10/modules/core/04-channel/types"
	ibctmtypes "github.com/cosmos/ibc-go/v10/modules/light-clients/07-tendermint"
	ibctesting "github.com/cosmos/ibc-go/v10/testing"
	"github.com/stretchr/testify/suite"

	store "cosmossdk.io/store/types"

	abci "github.com/cometbft/cometbft/abci/types"

	icstestingutils "github.com/cosmos/interchain-security/v7/testutil/ibc_testing"
	testutil "github.com/cosmos/interchain-security/v7/testutil/integration"
	consumertypes "github.com/cosmos/interchain-security/v7/x/ccv/consumer/types"
	ccv "github.com/cosmos/interchain-security/v7/x/ccv/types"
)

// Callback for instantiating a new coordinator with a provider test chains
// and provider app before every test defined on the suite.
type SetupProviderCallback func(t *testing.T) (
	coord *ibctesting.Coordinator,
	providerChain *ibctesting.TestChain,
	providerApp testutil.ProviderApp,
)

// Callback for instantiating a new consumer test chain
// and consumer app before every test defined on the suite.
type SetupConsumerCallback func(s *suite.Suite, coord *ibctesting.Coordinator, index int) (
	consumerBundle *icstestingutils.ConsumerBundle,
)

// CCVTestSuite is an in-mem test suite which implements the standard group of tests validating
// the integration functionality of ccv enabled chains.
// Any method implemented for this struct will be ran when suite.Run() is called.
type CCVTestSuite struct {
	suite.Suite
	coordinator           *ibctesting.Coordinator
	setupProviderCallback SetupProviderCallback
	setupConsumerCallback SetupConsumerCallback

	providerChain *ibctesting.TestChain
	providerApp   testutil.ProviderApp

	// The first consumer chain among multiple.
	consumerChain *ibctesting.TestChain
	// The first consumer app among multiple.
	consumerApp testutil.ConsumerApp
	// The ccv path to the first consumer among multiple.
	path *ibctesting.Path
	// The transfer path to the first consumer among multiple.
	transferPath *ibctesting.Path

	// A map from consumer id to its consumer bundle.
	// The preferred way to access chains, apps, and paths when designing tests around multiple consumers.
	consumerBundles map[string]*icstestingutils.ConsumerBundle
	skippedTests    map[string]bool

	// packetSniffers maps a chain and a packetSniffer
	packetSniffers map[*ibctesting.TestChain]*packetSniffer
}

// NewCCVTestSuite returns a new instance of CCVTestSuite, ready to be tested against using suite.Run().
func NewCCVTestSuite[Tp testutil.ProviderApp, Tc testutil.ConsumerApp](
	providerAppIniter ibctesting.AppCreator,
	consumerAppIniter icstestingutils.ValSetAppIniter,
	skippedTests []string,
) *CCVTestSuite {
	ccvSuite := new(CCVTestSuite)

	// Define callback to set up the provider chain
	ccvSuite.setupProviderCallback = func(t *testing.T) (
		*ibctesting.Coordinator,
		*ibctesting.TestChain,
		testutil.ProviderApp,
	) {
		t.Helper()
		// Instantiate the test coordinator.
		coordinator := ibctesting.NewCoordinator(t, 0)

		// Add provider to coordinator, store returned test chain and app.
		// Concrete provider app type is passed to the generic function here.
		provider, providerApp := icstestingutils.AddProvider[Tp](t, coordinator, providerAppIniter)

		// Pass variables to suite.
		return coordinator, provider, providerApp
	}

	ccvSuite.setupConsumerCallback = func(
		s *suite.Suite,
		coordinator *ibctesting.Coordinator,
		index int,
	) *icstestingutils.ConsumerBundle {
		return icstestingutils.AddConsumer[Tp, Tc](coordinator, s, index, consumerAppIniter)
	}

	ccvSuite.skippedTests = make(map[string]bool)
	for _, testName := range skippedTests {
		ccvSuite.skippedTests[testName] = true
	}
	return ccvSuite
}

func (suite *CCVTestSuite) BeforeTest(suiteName, testName string) {
	if suite.skippedTests[testName] {
		suite.T().Skip()
	}
}

// GetProviderChain returns the provider chain struct
// which is required to get context and have control over the blocks
func (suite *CCVTestSuite) GetProviderChain() *ibctesting.TestChain {
	return suite.providerChain
}

// GetCCVPath returns the CCV path which is
// required to call SetupCCVChannel
func (suite *CCVTestSuite) GetCCVPath() *ibctesting.Path {
	return suite.path
}

// SetupTest sets up in-mem state before every test
func (suite *CCVTestSuite) SetupTest() {
	suite.packetSniffers = make(map[*ibctesting.TestChain]*packetSniffer)

	// Instantiate new coordinator and provider chain using callback
	suite.coordinator, suite.providerChain,
		suite.providerApp = suite.setupProviderCallback(suite.T())
	suite.registerPacketSniffer(suite.providerChain)
	providerKeeper := suite.providerApp.GetProviderKeeper()

	// set `BlocksPerEpoch` to 10: a reasonable small value greater than 1 that prevents waiting for too
	// many blocks and slowing down the integration tests
	params := providerKeeper.GetParams(suite.providerCtx())
	params.BlocksPerEpoch = 10
	providerKeeper.SetParams(suite.providerCtx(), params)

	// start consumer chains
	suite.consumerBundles = make(map[string]*icstestingutils.ConsumerBundle)
	for i := 0; i < icstestingutils.NumConsumers; i++ {
		bundle := suite.setupConsumerCallback(&suite.Suite, suite.coordinator, i)
		suite.consumerBundles[bundle.ConsumerId] = bundle
		suite.registerPacketSniffer(bundle.Chain)

		// check that TopN is correctly set for the consumer
		powerShapingParameters, err := providerKeeper.GetConsumerPowerShapingParameters(suite.providerCtx(), bundle.ConsumerId)
		suite.Require().NoError(err)
		suite.Require().Equal(bundle.TopN, powerShapingParameters.Top_N)
	}

	// initialize each consumer chain with it's corresponding genesis state
	// stored on the provider.
	for consumerId := range suite.consumerBundles {
		consumerGenesisState, found := providerKeeper.GetConsumerGenesis(
			suite.providerCtx(),
			consumerId,
		)

		suite.Require().True(found, "consumer genesis not found")
		genesisState := consumertypes.GenesisState{
			Params:   consumerGenesisState.Params,
			Provider: consumerGenesisState.Provider,
			NewChain: consumerGenesisState.NewChain,
		}
		initConsumerChain(suite, consumerId, &genesisState)
	}

	// try updating all clients
	for _, bundle := range suite.consumerBundles {
		// try updating this consumer client on the provider chain
		err := bundle.Path.EndpointB.UpdateClient()
		suite.Require().NoError(err)

		// try updating the provider client on this consumer chain
		err = bundle.Path.EndpointA.UpdateClient()
		suite.Require().NoError(err)
	}
}

func (s *CCVTestSuite) registerPacketSniffer(chain *ibctesting.TestChain) {
	if s.packetSniffers == nil {
		s.packetSniffers = make(map[*ibctesting.TestChain]*packetSniffer)
	}
	p := newPacketSniffer()
	chain.App.GetBaseApp().SetStreamingManager(store.StreamingManager{
		ABCIListeners: []store.ABCIListener{p},
	})
	s.packetSniffers[chain] = p
}

func (s *CCVTestSuite) getSentPacket(chain *ibctesting.TestChain, sequence uint64, channelID string) (packet channeltypes.Packet, found bool) {
	key := getSentPacketKey(sequence, channelID)
	packet, found = s.packetSniffers[chain].packets[key]
	return
}

// initConsumerChain initializes a consumer chain given a genesis state
func initConsumerChain(
	s *CCVTestSuite,
	consumerId string,
	genesisState *consumertypes.GenesisState,
) {
	providerKeeper := s.providerApp.GetProviderKeeper()
	bundle := s.consumerBundles[consumerId]

	// run CCV module init genesis
	s.NotPanics(func() {
		consumerKeeper := bundle.GetKeeper()
		// this will set the initial valset on consumer
		consumerKeeper.InitGenesis(bundle.GetCtx(), genesisState)
	})

	// confirm client and cons state for consumer were set correctly in InitGenesis;
	// NOTE: on restart, both ProviderClientState and ProviderConsensusState are nil
	if genesisState.NewChain {
		consumerEndpointClientState,
			consumerEndpointConsState := s.GetConsumerEndpointClientAndConsState(*bundle)
		s.Require().Equal(genesisState.Provider.ClientState, consumerEndpointClientState)
		s.Require().Equal(genesisState.Provider.ConsensusState, consumerEndpointConsState)
	}

	// create path for the CCV channel
	bundle.Path = ibctesting.NewPath(bundle.Chain, s.providerChain)

	// Set provider endpoint's clientID for each consumer
	providerEndpointClientID, found := providerKeeper.GetConsumerClientId(
		s.providerCtx(),
		consumerId,
	)
	s.Require().True(found, "provider endpoint clientID not found")
	bundle.Path.EndpointB.ClientID = providerEndpointClientID
	// Set consumer endpoint's clientID
	consumerKeeper := bundle.GetKeeper()
	consumerEndpointClientID, found := consumerKeeper.GetProviderClientID(bundle.GetCtx())
	s.Require().True(found, "consumer endpoint clientID not found")
	bundle.Path.EndpointA.ClientID = consumerEndpointClientID

	// Note: suite.path.EndpointA.ClientConfig and suite.path.EndpointB.ClientConfig are not populated,
	// since these IBC testing package fields are unused in our tests.

	// Confirm client config is now correct
	s.validateEndpointsClientConfig(*bundle)

	// - channel config
	bundle.Path.EndpointA.ChannelConfig.PortID = ccv.ConsumerPortID
	bundle.Path.EndpointB.ChannelConfig.PortID = ccv.ProviderPortID
	bundle.Path.EndpointA.ChannelConfig.Version = ccv.Version
	bundle.Path.EndpointB.ChannelConfig.Version = ccv.Version
	bundle.Path.EndpointA.ChannelConfig.Order = channeltypes.ORDERED
	bundle.Path.EndpointB.ChannelConfig.Order = channeltypes.ORDERED

	// create path for the transfer channel
	bundle.TransferPath = ibctesting.NewPath(bundle.Chain, s.providerChain)
	bundle.TransferPath.EndpointA.ChannelConfig.PortID = transfertypes.PortID
	bundle.TransferPath.EndpointB.ChannelConfig.PortID = transfertypes.PortID
	bundle.TransferPath.EndpointA.ChannelConfig.Version = transfertypes.V1
	bundle.TransferPath.EndpointB.ChannelConfig.Version = transfertypes.V1

	// commit state on this consumer chain
	s.coordinator.CommitBlock(bundle.Chain)

	// try updating this consumer client on the provider chain
	err := bundle.Path.EndpointB.UpdateClient()
	s.Require().NoError(err)

	// try updating the provider client on this consumer chain
	err = bundle.Path.EndpointA.UpdateClient()
	s.Require().NoError(err)

	if consumerId == icstestingutils.FirstConsumerID {
		// Support tests that were written before multiple consumers were supported.
		firstBundle := s.getFirstBundle()
		s.consumerApp = firstBundle.App
		s.consumerChain = firstBundle.Chain
		s.path = firstBundle.Path
		s.transferPath = firstBundle.TransferPath
	}
}

func (suite *CCVTestSuite) SetupAllCCVChannels() {
	for _, bundle := range suite.consumerBundles {
		suite.SetupCCVChannel(bundle.Path)
	}
}

func (suite *CCVTestSuite) SetupCCVChannel(path *ibctesting.Path) {
	path.CreateConnections()
	path.CreateChannels()
}

// TODO: Make SetupTransferChannel functional for multiple consumers by pattern matching SetupCCVChannel.
// See: https://github.com/cosmos/interchain-security/issues/506
// SetupTransferChannel setup the transfer channel of the first consumer chain among multiple
func (suite *CCVTestSuite) SetupTransferChannel() {
	suite.setupTransferChannel(
		suite.transferPath,
		suite.path,
		suite.consumerApp.GetConsumerKeeper().GetDistributionTransmissionChannel(
			suite.consumerChain.GetContext(),
		),
	)
}

func (suite *CCVTestSuite) setupTransferChannel(
	transferPath *ibctesting.Path,
	ccvPath *ibctesting.Path,
	channelID string,
) {
	// transfer path will use the same connection as ccv path
	transferPath.EndpointA.ClientID = ccvPath.EndpointA.ClientID
	transferPath.EndpointA.ConnectionID = ccvPath.EndpointA.ConnectionID
	transferPath.EndpointB.ClientID = ccvPath.EndpointB.ClientID
	transferPath.EndpointB.ConnectionID = ccvPath.EndpointB.ConnectionID

	// CCV channel handshake will automatically initiate transfer channel handshake on ACK
	// so transfer channel will be on stage INIT when CompleteSetupCCVChannel returns.
	transferPath.EndpointA.ChannelID = channelID

	// Complete TRY, ACK, CONFIRM for transfer path
	err := transferPath.EndpointB.ChanOpenTry()
	suite.Require().NoError(err)

	err = transferPath.EndpointA.ChanOpenAck()
	suite.Require().NoError(err)

	err = transferPath.EndpointB.ChanOpenConfirm()
	suite.Require().NoError(err)

	// ensure counterparty is up to date
	err = transferPath.EndpointA.UpdateClient()
	suite.Require().NoError(err)
}

// SetupAllTransferChannel setup all consumer chains transfer channel
func (suite *CCVTestSuite) SetupAllTransferChannels() {
	// setup the first consumer transfer channel
	suite.SetupTransferChannel()

	// setup all the remaining consumers transfer channels
	for consumerId := range suite.consumerBundles {
		// skip fist consumer
		if consumerId == suite.getFirstBundle().ConsumerId {
			continue
		}

		// get the bundle for the chain ID
		bundle := suite.consumerBundles[consumerId]
		// setup the transfer channel
		suite.setupTransferChannel(
			bundle.TransferPath,
			bundle.Path,
			bundle.App.GetConsumerKeeper().GetDistributionTransmissionChannel(bundle.GetCtx()),
		)
	}
}

func (s *CCVTestSuite) validateEndpointsClientConfig(consumerBundle icstestingutils.ConsumerBundle) {
	consumerKeeper := consumerBundle.GetKeeper()
	providerStakingKeeper := s.providerApp.GetTestStakingKeeper()

	consumerUnbondingPeriod := consumerKeeper.GetUnbondingPeriod(consumerBundle.GetCtx())
	cs, ok := s.providerApp.GetIBCKeeper().ClientKeeper.GetClientState(s.providerCtx(),
		consumerBundle.Path.EndpointB.ClientID)
	s.Require().True(ok)
	s.Require().Equal(
		consumerUnbondingPeriod,
		cs.(*ibctmtypes.ClientState).UnbondingPeriod,
		"unexpected unbonding period in consumer client state",
	)

	providerUnbondingPeriod, err := providerStakingKeeper.UnbondingTime(s.providerCtx())
	s.Require().NoError(err)
	cs, ok = consumerBundle.App.GetIBCKeeper().ClientKeeper.GetClientState(
		consumerBundle.GetCtx(), consumerBundle.Path.EndpointA.ClientID)
	s.Require().True(ok)
	s.Require().Equal(
		providerUnbondingPeriod,
		cs.(*ibctmtypes.ClientState).UnbondingPeriod,
		"unexpected unbonding period in provider client state",
	)
}

// packetSniffer implements the StreamingService interface.
// Implements ListenEndBlock to record packets from events.
type packetSniffer struct {
	packets map[string]channeltypes.Packet
}

var _ store.ABCIListener = &packetSniffer{}

func newPacketSniffer() *packetSniffer {
	return &packetSniffer{
		packets: make(map[string]channeltypes.Packet),
	}
}

func (ps *packetSniffer) ListenFinalizeBlock(ctx context.Context, req abci.RequestFinalizeBlock, res abci.ResponseFinalizeBlock) error {
	packets := ParsePacketsFromEvents(res.GetEvents())
	for _, packet := range packets {
		ps.packets[getSentPacketKey(packet.Sequence, packet.SourceChannel)] = packet
	}
	return nil
}

// getSentPacketKey returns a key for accessing a sent packet,
// given an ibc sequence number and the channel ID for the source endpoint.
func getSentPacketKey(sequence uint64, channelID string) string {
	return fmt.Sprintf("%s-%d", channelID, sequence)
}

func (*packetSniffer) ListenCommit(ctx context.Context, res abci.ResponseCommit, cs []*store.StoreKVPair) error {
	return nil
}

// ParsePacketsFromEvents returns all packets found in events.
func ParsePacketsFromEvents(events []abci.Event) (packets []channeltypes.Packet) {
	for i, ev := range events {
		if ev.Type == channeltypes.EventTypeSendPacket {
			packet, err := ibctesting.ParsePacketFromEvents(events[i:])
			if err != nil {
				panic(err)
			}
			packets = append(packets, packet)
		}
	}
	return
}
