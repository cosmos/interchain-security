package provider_test

import (
	"testing"

	sdk "github.com/cosmos/cosmos-sdk/types"
	distrtypes "github.com/cosmos/cosmos-sdk/x/distribution/types"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	commitmenttypes "github.com/cosmos/ibc-go/v3/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"

	appConsumer "github.com/cosmos/interchain-security/app_consumer"
	appProvider "github.com/cosmos/interchain-security/app_provider"
	"github.com/cosmos/interchain-security/testutil/simapp"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	"github.com/cosmos/interchain-security/x/ccv/types"

	tmtypes "github.com/tendermint/tendermint/types"

	"github.com/stretchr/testify/suite"
)

type PBTTestSuite struct {
	suite.Suite

	coordinator *ibctesting.Coordinator

	// testing chains
	providerChain *ibctesting.TestChain
	consumerChain *ibctesting.TestChain

	providerClient    *ibctmtypes.ClientState
	providerConsState *ibctmtypes.ConsensusState
	consumerClient    *ibctmtypes.ClientState
	consumerConsState *ibctmtypes.ConsensusState

	path *ibctesting.Path

	ctx sdk.Context
}

func TestPBTTestSuite(t *testing.T) {
	suite.Run(t, new(ProviderTestSuite))
}

func (suite *PBTTestSuite) SetupTest() {

	suite.coordinator, suite.providerChain, suite.consumerChain = simapp.NewProviderConsumerCoordinator(suite.T())

	suite.DisableConsumerDistribution()

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

	valUpdates := tmtypes.TM2PB.ValidatorUpdates(suite.providerChain.Vals)

	params := consumertypes.NewParams(
		true,
		1000, // about 2 hr at 7.6 seconds per blocks
		"",
		"",
		"0.5", // 50%
	)
	consumerGenesis := consumertypes.NewInitialGenesisState(suite.providerClient, suite.providerConsState, valUpdates, params)
	suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.InitGenesis(suite.consumerChain.GetContext(), consumerGenesis)

	suite.ctx = suite.providerChain.GetContext()

	suite.path = ibctesting.NewPath(suite.consumerChain, suite.providerChain)
	suite.path.EndpointA.ChannelConfig.PortID = consumertypes.PortID
	suite.path.EndpointB.ChannelConfig.PortID = providertypes.PortID
	suite.path.EndpointA.ChannelConfig.Version = types.Version
	suite.path.EndpointB.ChannelConfig.Version = types.Version
	suite.path.EndpointA.ChannelConfig.Order = channeltypes.ORDERED
	suite.path.EndpointB.ChannelConfig.Order = channeltypes.ORDERED
	providerClient, ok := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetProviderClient(suite.consumerChain.GetContext())
	if !ok {
		panic("must already have provider client on consumer chain")
	}
	// set consumer endpoint's clientID
	suite.path.EndpointA.ClientID = providerClient

	// TODO: No idea why or how this works, but it seems that it needs to be done.
	suite.path.EndpointB.Chain.SenderAccount.SetAccountNumber(6)
	suite.path.EndpointA.Chain.SenderAccount.SetAccountNumber(6)

	// create consumer client on provider chain and set as consumer client for consumer chainID in provider keeper.
	suite.path.EndpointB.CreateClient()
	suite.providerChain.App.(*appProvider.App).ProviderKeeper.SetConsumerClient(suite.providerChain.GetContext(), suite.consumerChain.ChainID, suite.path.EndpointB.ClientID)
}

// TODO: clear up these hacks after stripping provider/consumer
func (s *PBTTestSuite) DisableConsumerDistribution() {
	cChain := s.consumerChain
	cApp := cChain.App.(*appConsumer.App)
	for i, moduleName := range cApp.MM.OrderBeginBlockers {
		if moduleName == distrtypes.ModuleName {
			cApp.MM.OrderBeginBlockers = append(cApp.MM.OrderBeginBlockers[:i], cApp.MM.OrderBeginBlockers[i+1:]...)
			return
		}
	}
}

type DelegateAction struct {
	del     string
	val     string
	amt     int64
	succeed bool
}
type UndelegateAction struct {
	del     string
	val     string
	amt     int64
	succeed bool
}
type BeginRedelegateAction struct {
	del       string
	valSrc    string
	valDst    string
	amt       int
	succeed64 bool
}
type ProviderSlashAction struct {
	val              string
	infractionHeight int64
	power            int64
	slashFactor      float64
}
type ProviderJailAction struct{}
type ProviderUnjailAction struct{}
type ProviderJumpToBlock struct {
	height int64
}
type ConsumerSlashAction struct{}
type ConsumerJumpToBlock struct {
	height int64
}

func TestDummy(t *testing.T) {

}
