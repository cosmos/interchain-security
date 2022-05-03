package keeper_test

import (
	"testing"

	sdk "github.com/cosmos/cosmos-sdk/types"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	commitmenttypes "github.com/cosmos/ibc-go/v3/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"

	"github.com/cosmos/interchain-security/app"
	"github.com/cosmos/interchain-security/testutil/simapp"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	"github.com/cosmos/interchain-security/x/ccv/types"

	tmtypes "github.com/tendermint/tendermint/types"

	"github.com/stretchr/testify/suite"
)

func init() {
	ibctesting.DefaultTestingAppInit = simapp.SetupTestingApp
}

type KeeperTestSuite struct {
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

func (suite *KeeperTestSuite) SetupTest() {
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

	valUpdates := tmtypes.TM2PB.ValidatorUpdates(suite.providerChain.Vals)

	params := consumertypes.DefaultParams()
	params.Enabled = true
	consumerGenesis := consumertypes.NewInitialGenesisState(suite.providerClient, suite.providerConsState, valUpdates, params)
	suite.consumerChain.App.(*app.App).ConsumerKeeper.InitGenesis(suite.consumerChain.GetContext(), consumerGenesis)

	suite.ctx = suite.providerChain.GetContext()

	suite.path = ibctesting.NewPath(suite.consumerChain, suite.providerChain)
	suite.path.EndpointA.ChannelConfig.PortID = consumertypes.PortID
	suite.path.EndpointB.ChannelConfig.PortID = providertypes.PortID
	suite.path.EndpointA.ChannelConfig.Version = types.Version
	suite.path.EndpointB.ChannelConfig.Version = types.Version
	suite.path.EndpointA.ChannelConfig.Order = channeltypes.ORDERED
	suite.path.EndpointB.ChannelConfig.Order = channeltypes.ORDERED
	providerClient, ok := suite.consumerChain.App.(*app.App).ConsumerKeeper.GetProviderClient(suite.consumerChain.GetContext())
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
	suite.providerChain.App.(*app.App).ProviderKeeper.SetConsumerClient(suite.providerChain.GetContext(), suite.consumerChain.ChainID, suite.path.EndpointB.ClientID)
}

func TestKeeperTestSuite(t *testing.T) {
	suite.Run(t, new(KeeperTestSuite))
}

func (suite *KeeperTestSuite) TestValsetUpdateBlockHeight() {
	app := suite.providerChain.App.(*app.App)
	ctx := suite.ctx

	blockHeight := app.ProviderKeeper.GetValsetUpdateBlockHeight(ctx, uint64(0))
	suite.Require().Zero(blockHeight)

	app.ProviderKeeper.SetValsetUpdateBlockHeight(ctx, uint64(1), uint64(2))
	blockHeight = app.ProviderKeeper.GetValsetUpdateBlockHeight(ctx, uint64(1))
	suite.Require().Equal(blockHeight, uint64(2))

	app.ProviderKeeper.DeleteValsetUpdateBlockHeight(ctx, uint64(1))
	blockHeight = app.ProviderKeeper.GetValsetUpdateBlockHeight(ctx, uint64(1))
	suite.Require().Zero(blockHeight)

	app.ProviderKeeper.SetValsetUpdateBlockHeight(ctx, uint64(1), uint64(2))
	app.ProviderKeeper.SetValsetUpdateBlockHeight(ctx, uint64(3), uint64(4))
	blockHeight = app.ProviderKeeper.GetValsetUpdateBlockHeight(ctx, uint64(3))
	suite.Require().Equal(blockHeight, uint64(4))
}

func (suite *KeeperTestSuite) TestSlashAcks() {
	app := suite.providerChain.App.(*app.App)
	ctx := suite.ctx

	var chainsAcks [][]string

	penaltiesfN := func() (penalties []string) {
		app.ProviderKeeper.IterateSlashAcks(ctx, func(id string, acks []string) bool {
			chainsAcks = append(chainsAcks, acks)
			return true
		})
		return
	}

	chainID := "consumer"

	acks := app.ProviderKeeper.GetSlashAcks(ctx, chainID)
	suite.Require().Nil(acks)

	p := []string{"alice", "bob", "charlie"}
	app.ProviderKeeper.SetSlashAcks(ctx, chainID, p)

	acks = app.ProviderKeeper.GetSlashAcks(ctx, chainID)
	suite.Require().NotNil(acks)

	suite.Require().Len(acks, 3)
	emptied := app.ProviderKeeper.EmptySlashAcks(ctx, chainID)
	suite.Require().Len(emptied, 3)

	acks = app.ProviderKeeper.GetSlashAcks(ctx, chainID)
	suite.Require().Nil(acks)

	chains := []string{"c1", "c2", "c3"}

	for _, c := range chains {
		app.ProviderKeeper.SetSlashAcks(ctx, c, p)
	}

	penaltiesfN()
	suite.Require().Len(chainsAcks, len(chains))
}

func (suite *KeeperTestSuite) TestAppendslashingAck() {
	app := suite.providerChain.App.(*app.App)
	ctx := suite.ctx

	p := []string{"alice", "bob", "charlie"}
	chains := []string{"c1", "c2"}
	app.ProviderKeeper.SetSlashAcks(ctx, chains[0], p)

	app.ProviderKeeper.AppendslashingAck(ctx, chains[0], p[0])
	acks := app.ProviderKeeper.GetSlashAcks(ctx, chains[0])
	suite.Require().NotNil(acks)
	suite.Require().Len(acks, len(p)+1)

	app.ProviderKeeper.AppendslashingAck(ctx, chains[1], p[0])
	acks = app.ProviderKeeper.GetSlashAcks(ctx, chains[1])
	suite.Require().NotNil(acks)
	suite.Require().Len(acks, 1)
}

func (suite *KeeperTestSuite) TestInitHeight() {
	app := suite.providerChain.App.(*app.App)
	ctx := suite.ctx

	tc := []struct {
		chainID  string
		expected uint64
	}{
		{expected: 0, chainID: "chain"},
		{expected: 10, chainID: "chain1"},
		{expected: 12, chainID: "chain2"},
	}

	app.ProviderKeeper.SetInitChainHeight(ctx, tc[1].chainID, tc[1].expected)
	app.ProviderKeeper.SetInitChainHeight(ctx, tc[2].chainID, tc[2].expected)

	for _, t := range tc {
		height := app.ProviderKeeper.GetInitChainHeight(ctx, t.chainID)
		suite.Require().EqualValues(t.expected, height)
	}
}
