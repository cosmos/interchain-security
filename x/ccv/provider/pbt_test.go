package provider_test

import (
	"testing"

	sdk "github.com/cosmos/cosmos-sdk/types"
	distrtypes "github.com/cosmos/cosmos-sdk/x/distribution/types"
	"github.com/stretchr/testify/suite"

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

	stakingkeeper "github.com/cosmos/cosmos-sdk/x/staking/keeper"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
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

	providerCtx sdk.Context
	consumerCtx sdk.Context

	path *ibctesting.Path
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

	s.providerClient = ibctmtypes.NewClientState(
		s.providerChain.ChainID, tmConfig.TrustLevel, tmConfig.TrustingPeriod, tmConfig.UnbondingPeriod, tmConfig.MaxClockDrift,
		height, commitmenttypes.GetSDKSpecs(), UpgradePath, tmConfig.AllowUpdateAfterExpiry, tmConfig.AllowUpdateAfterMisbehaviour,
	)
	s.providerConsState = s.providerChain.LastHeader.ConsensusState()

	valUpdates := tmtypes.TM2PB.ValidatorUpdates(s.providerChain.Vals)

	params := consumertypes.NewParams(
		true,
		1000, // about 2 hr at 7.6 seconds per blocks
		"",
		"",
		"0.5", // 50%
	)
	consumerGenesis := consumertypes.NewInitialGenesisState(s.providerClient, s.providerConsState, valUpdates, params)
	s.consumerChain.App.(*appConsumer.App).ConsumerKeeper.InitGenesis(s.consumerChain.GetContext(), consumerGenesis)

	s.providerCtx = s.providerChain.GetContext()

	s.path = ibctesting.NewPath(s.consumerChain, s.providerChain)
	s.path.EndpointA.ChannelConfig.PortID = consumertypes.PortID
	s.path.EndpointB.ChannelConfig.PortID = providertypes.PortID
	s.path.EndpointA.ChannelConfig.Version = types.Version
	s.path.EndpointB.ChannelConfig.Version = types.Version
	s.path.EndpointA.ChannelConfig.Order = channeltypes.ORDERED
	s.path.EndpointB.ChannelConfig.Order = channeltypes.ORDERED
	providerClient, ok := s.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetProviderClient(s.consumerChain.GetContext())
	if !ok {
		panic("must already have provider client on consumer chain")
	}
	// set consumer endpoint's clientID
	s.path.EndpointA.ClientID = providerClient

	// TODO: No idea why or how this works, but it seems that it needs to be done.
	s.path.EndpointB.Chain.SenderAccount.SetAccountNumber(6)
	s.path.EndpointA.Chain.SenderAccount.SetAccountNumber(6)

	// create consumer client on provider chain and set as consumer client for consumer chainID in provider keeper.
	s.path.EndpointB.CreateClient()
	s.providerChain.App.(*appProvider.App).ProviderKeeper.SetConsumerClient(s.providerChain.GetContext(), s.consumerChain.ChainID, s.path.EndpointB.ClientID)

	// TODO: I added this section
	//~~~~~~~~~~

	s.coordinator.CreateConnections(s.path)

	// CCV channel handshake will automatically initiate transfer channel handshake on ACK
	// so transfer channel will be on stage INIT when CreateChannels for ccv path returns.
	s.coordinator.CreateChannels(s.path)
	//~~~~~~~~~~

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

type Action struct {
	kind             string
	valSrc           int
	valDst           int
	amt              int
	succeed          bool
	chain            string
	height           int
	infractionHeight int
	power            int
	slashPercentage  int
}
type DelegateAction struct {
	val     int
	amt     int
	succeed bool
}
type UndelegateAction struct {
	val     int
	amt     int
	succeed bool
}
type BeginRedelegateAction struct {
	valSrc  int
	valDst  int
	amt     int
	succeed bool
}
type ProviderSlashAction struct {
	val              int
	infractionHeight int
	power            int
	slashPercentage  int
}
type ConsumerSlashAction struct {
	val              int
	infractionHeight int
	power            int
	slashPercentage  int
}
type JumpToBlockAction struct {
	chain  string
	height int
}
type DeliverAction struct {
	chain string
}

func scaledAmt(modelAmt int) sdk.Int {
	return sdk.TokensFromConsensusPower(int64(modelAmt), sdk.DefaultPowerReduction)
}

func getDelegator(s *PBTTestSuite) sdk.AccAddress {
	delAddr := s.providerChain.SenderAccount.GetAddress()
	return delAddr

}

func getValidator(s *PBTTestSuite, i int) sdk.ValAddress {
	tmValidator := s.providerChain.Vals.Validators[0]
	valAddr, err := sdk.ValAddressFromHex(tmValidator.Address.String())
	s.Require().NoError(err)
	return valAddr
}

func getConsAddr(s *PBTTestSuite, i int) sdk.ConsAddress {
	val := s.providerChain.Vals.Validators[0]
	consAddr := sdk.ConsAddress(val.Address)
	return consAddr
}

// TODO: it's here!~~~~~~

func (s *PBTTestSuite) delegate(a DelegateAction) {
	psk := s.providerChain.App.GetStakingKeeper()
	pskServer := stakingkeeper.NewMsgServerImpl(psk)
	denom := sdk.DefaultBondDenom
	amt := sdk.NewCoin(denom, scaledAmt(int(a.amt)))
	del := getDelegator(s)
	val := getValidator(s, a.val)
	msg := stakingtypes.NewMsgDelegate(del, val, amt)
	pskServer.Delegate(sdk.WrapSDKContext(s.providerCtx), msg)
}

func (s *PBTTestSuite) undelegate(a UndelegateAction) {

	psk := s.providerChain.App.GetStakingKeeper()
	pskServer := stakingkeeper.NewMsgServerImpl(psk)
	denom := sdk.DefaultBondDenom
	amt := sdk.NewCoin(denom, scaledAmt(a.amt))
	del := getDelegator(s)
	val := getValidator(s, a.val)
	msg := stakingtypes.NewMsgUndelegate(del, val, amt)
	pskServer.Undelegate(sdk.WrapSDKContext(s.providerCtx), msg)
}

func (s *PBTTestSuite) beginRedelegate(a BeginRedelegateAction) {

	psk := s.providerChain.App.GetStakingKeeper()
	pskServer := stakingkeeper.NewMsgServerImpl(psk)

	denom := sdk.DefaultBondDenom
	amt := sdk.NewCoin(denom, scaledAmt(a.amt))
	del := getDelegator(s)
	valSrc := getValidator(s, a.valSrc)
	valDst := getValidator(s, a.valDst)
	msg := stakingtypes.NewMsgBeginRedelegate(del, valSrc, valDst, amt)
	pskServer.BeginRedelegate(sdk.WrapSDKContext(s.providerCtx), msg)
}

func (s *PBTTestSuite) providerSlash(a ProviderSlashAction) {
	psk := s.providerChain.App.GetStakingKeeper()
	val := getConsAddr(s, a.val)
	h := int64(a.infractionHeight)
	power := int64(a.power)
	factor := sdk.NewDec(int64(a.slashPercentage)) // TODO: I think it's a percentage (from 100)?
	psk.Slash(s.providerCtx, val, h, power, factor)
}

func (s *PBTTestSuite) consumerSlash(a ConsumerSlashAction) {
	cccvk := s.consumerChain.App.(*appConsumer.App).ConsumerKeeper
	val := getConsAddr(s, a.val)
	h := int64(a.infractionHeight)
	power := int64(a.power)
	factor := sdk.NewDec(int64(a.slashPercentage)) // TODO: I think it's a percentage (from 100)?
	cccvk.Slash(s.consumerCtx, val, h, power, factor)
}

func (s *PBTTestSuite) jumpToBlock(a JumpToBlockAction) {
	h := int64(a.height)
	m := make(map[string]*ibctesting.TestChain)
	m["provider"] = s.providerChain
	m["consumer"] = s.consumerChain
	hCurr := m[a.chain].CurrentHeader.Height
	s.Assert().LessOrEqual(int64(0), h-hCurr)
	dt := uint64(h - hCurr)
	s.coordinator.CommitNBlocks(m[a.chain], dt)
}

func (s *PBTTestSuite) deliver(a DeliverAction) {
}

func executeTrace(s *PBTTestSuite, trace []Action) {

	for _, a := range trace {
		// succeed := a.succeed
		switch a.kind {
		case "delegate":
			s.delegate(DelegateAction{
				a.valDst,
				a.amt,
				a.succeed,
			})
		case "undelegate":
			s.undelegate(UndelegateAction{
				a.valDst,
				a.amt,
				a.succeed,
			})
		case "beginRedelegate":
			s.beginRedelegate(BeginRedelegateAction{
				a.valSrc,
				a.valDst,
				a.amt,
				a.succeed,
			})
		case "providerSlash":
			s.providerSlash(ProviderSlashAction{
				a.valDst,
				a.infractionHeight,
				a.power,
				a.slashPercentage,
			})
		case "consumerSlash":
			s.consumerSlash(ConsumerSlashAction{
				a.valDst,
				a.infractionHeight,
				a.power,
				a.slashPercentage,
			})
		case "jumpToBlock":
			s.jumpToBlock(JumpToBlockAction{
				a.chain,
				a.height,
			})
		case "deliver":
			s.deliver(DeliverAction{a.chain})
		}

	}
}

func (s *PBTTestSuite) TestTrace() {

	trace := []Action{
		{
			kind:    "delegate",
			valDst:  0,
			amt:     1,
			succeed: true,
		},
		{
			kind:    "undelegate",
			valDst:  0,
			amt:     1,
			succeed: true,
		},
		{
			kind:    "beginRedelegate",
			valSrc:  0,
			valDst:  1,
			amt:     1,
			succeed: true,
		},
		{
			kind:             "providerSlash",
			valDst:           0,
			infractionHeight: 22,
			power:            1,
			slashPercentage:  5,
		},
		{
			kind:             "consumerSlash",
			valDst:           0,
			infractionHeight: 22,
			power:            0,
			slashPercentage:  5,
		},
		{
			kind:   "jumpToBlock",
			chain:  "provider",
			height: 22,
		},
		{
			kind:  "deliver",
			chain: "provider",
		},
	}

	executeTrace(s, trace)

}
