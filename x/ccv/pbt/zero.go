package provider_test

import (
	"testing"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/stretchr/testify/suite"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	commitmenttypes "github.com/cosmos/ibc-go/v3/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"

	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	appProvider "github.com/cosmos/interchain-security/app/provider"
	"github.com/cosmos/interchain-security/testutil/simapp"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	"github.com/cosmos/interchain-security/x/ccv/types"

	tmtypes "github.com/tendermint/tendermint/types"
)

type PBTTestSuite struct {
	suite.Suite

	coordinator *ibctesting.Coordinator

	// testing chains
	providerChain *ibctesting.TestChain
	consumerChain *ibctesting.TestChain

	path *ibctesting.Path
}

const P = "provider"
const C = "consumer"

// TODO: do I need different denoms for each chain?
const denom = sdk.DefaultBondDenom
const maxValidators = 2

func init() {
	// Tokens = Power
	sdk.DefaultPowerReduction = sdk.NewInt(1)
}

func TestPBTTestSuite(t *testing.T) {
	suite.Run(t, new(PBTTestSuite))
}

func (s *PBTTestSuite) SetupTest() {

	s.coordinator, s.providerChain, s.consumerChain = simapp.NewProviderConsumerCoordinator(s.T())

	s.DisableConsumerDistribution()

	tmConfig := ibctesting.NewTendermintConfig()

	// commit a block on provider chain before creating client
	s.coordinator.CommitBlock(s.providerChain)

	// create client and consensus state of provider chain to initialize consumer chain genesis.
	height := s.providerChain.LastHeader.GetHeight().(clienttypes.Height)
	UpgradePath := []string{"upgrade", "upgradedIBCState"}

	providerClient := ibctmtypes.NewClientState(
		s.providerChain.ChainID, tmConfig.TrustLevel, tmConfig.TrustingPeriod, tmConfig.UnbondingPeriod, tmConfig.MaxClockDrift,
		height, commitmenttypes.GetSDKSpecs(), UpgradePath, tmConfig.AllowUpdateAfterExpiry, tmConfig.AllowUpdateAfterMisbehaviour,
	)
	providerConsState := s.providerChain.LastHeader.ConsensusState()

	valUpdates := tmtypes.TM2PB.ValidatorUpdates(s.providerChain.Vals)

	params := consumertypes.NewParams(
		true,
		1000, // about 2 hr at 7.6 seconds per blocks
		"",
		"",
		"0.5", // 50%
	)
	consumerGenesis := consumertypes.NewInitialGenesisState(providerClient, providerConsState, valUpdates, params)
	s.consumerChain.App.(*appConsumer.App).ConsumerKeeper.InitGenesis(s.ctx(C), consumerGenesis)

	s.path = ibctesting.NewPath(s.consumerChain, s.providerChain)
	s.path.EndpointA.ChannelConfig.PortID = consumertypes.PortID
	s.path.EndpointB.ChannelConfig.PortID = providertypes.PortID
	s.path.EndpointA.ChannelConfig.Version = types.Version
	s.path.EndpointB.ChannelConfig.Version = types.Version
	s.path.EndpointA.ChannelConfig.Order = channeltypes.ORDERED
	s.path.EndpointB.ChannelConfig.Order = channeltypes.ORDERED

	providerClientId, ok := s.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetProviderClient(s.ctx(C))
	if !ok {
		panic("must already have provider client on consumer chain")
	}

	// set consumer endpoint's clientID
	s.path.EndpointA.ClientID = providerClientId

	// TODO: No idea why or how this works, but it seems that it needs to be done.
	s.path.EndpointB.Chain.SenderAccount.SetAccountNumber(6)
	s.path.EndpointA.Chain.SenderAccount.SetAccountNumber(6)

	// create consumer client on provider chain and set as consumer client for consumer chainID in provider keeper.
	s.path.EndpointB.CreateClient()
	s.providerChain.App.(*appProvider.App).ProviderKeeper.SetConsumerClient(s.ctx(P), s.consumerChain.ChainID, s.path.EndpointB.ClientID)

	// TODO: I added this section, should I remove it or move it?
	//~~~~~~~~~~
	s.coordinator.CreateConnections(s.path)

	// CCV channel handshake will automatically initiate transfer channel handshake on ACK
	// so transfer channel will be on stage INIT when CreateChannels for ccv path returns.
	s.coordinator.CreateChannels(s.path)
	//~~~~~~~~~~

}
