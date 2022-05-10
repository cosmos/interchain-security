package provider_test

import (
	"fmt"
	"testing"

	sdk "github.com/cosmos/cosmos-sdk/types"
	distrtypes "github.com/cosmos/cosmos-sdk/x/distribution/types"
	"github.com/stretchr/testify/require"
	"github.com/stretchr/testify/suite"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	commitmenttypes "github.com/cosmos/ibc-go/v3/modules/core/23-commitment/types"
	exported "github.com/cosmos/ibc-go/v3/modules/core/exported"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"

	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	appProvider "github.com/cosmos/interchain-security/app/provider"
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

const p = "provider"
const c = "consumer"

// TODO: do I need different denoms for each chain?
const denom = sdk.DefaultBondDenom
const maxValidators = 3

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

	// TODO: I added this section, should I remove it or move it?
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
	valSrc           int64
	valDst           int64
	amt              int64
	succeed          bool
	chain            string
	height           int64
	infractionHeight int64
	power            int64
	slashPercentage  int64
}
type DelegateAction struct {
	val     int64
	amt     int64
	succeed bool
}
type UndelegateAction struct {
	val     int64
	amt     int64
	succeed bool
}
type BeginRedelegateAction struct {
	valSrc  int64
	valDst  int64
	amt     int64
	succeed bool
}
type ProviderSlashAction struct {
	val              int64
	infractionHeight int64
	power            int64
	slashPercentage  int64
}
type ConsumerSlashAction struct {
	val              int64
	infractionHeight int64
	power            int64
	slashPercentage  int64
}
type JumpToBlockAction struct {
	chain  string
	height int64
}
type UpdateClientAction struct {
	chain string
}

func (s *PBTTestSuite) chain(chain string) *ibctesting.TestChain {
	chains := make(map[string]*ibctesting.TestChain)
	chains["provider"] = s.providerChain
	chains["consumer"] = s.consumerChain
	return chains[chain]
}

func (s *PBTTestSuite) endpoint(chain string) *ibctesting.Endpoint {
	endpoints := make(map[string]*ibctesting.Endpoint)
	endpoints["provider"] = s.path.EndpointB
	endpoints["consumer"] = s.path.EndpointA
	return endpoints[chain]
}

func (s *PBTTestSuite) ctx(chain string) *sdk.Context {
	ctxs := make(map[string]*sdk.Context)
	ctxs["provider"] = &s.providerCtx //TODO: is using passbyvalue ctx on the suite ok?
	ctxs["consumer"] = &s.consumerCtx
	return ctxs[chain]
}

func (s *PBTTestSuite) delegator() sdk.AccAddress {
	delAddr := s.providerChain.SenderAccount.GetAddress()
	return delAddr
}

func (s *PBTTestSuite) validator(i int64) sdk.ValAddress {
	tmValidator := s.providerChain.Vals.Validators[i]
	valAddr, err := sdk.ValAddressFromHex(tmValidator.Address.String())
	s.Require().NoError(err)
	return valAddr
}

func (s *PBTTestSuite) consAddr(i int64) sdk.ConsAddress {
	val := s.providerChain.Vals.Validators[i]
	consAddr := sdk.ConsAddress(val.Address)
	return consAddr
}

func (s *PBTTestSuite) validatorStatus(chain string, i int64) stakingtypes.BondStatus {
	addr := s.validator(i)
	val, found := s.chain(chain).App.GetStakingKeeper().GetValidator(*s.ctx(chain), addr)
	if !found {
		s.T().Fatal("Couldn't GetValidator")
	}
	return val.GetStatus()
}

// TODO: this is probably useless
func (s *PBTTestSuite) delegatorBalance() int64 {
	del := s.delegator()
	app := s.providerChain.App.(*appProvider.App)
	bal := app.BankKeeper.GetBalance(s.providerCtx, del, denom)
	return bal.Amount.Int64()
}

func (s *PBTTestSuite) validatorTokens(chain string, i int64) int64 {
	addr := s.validator(i)
	val, found := s.chain(chain).App.GetStakingKeeper().GetValidator(*s.ctx(chain), addr)
	if !found {
		s.T().Fatal("Couldn't GetValidator")
	}
	return val.Tokens.Int64()
}

func (s *PBTTestSuite) delegation(i int64) int64 {
	addr := s.delegator()
	del, found := s.providerChain.App.GetStakingKeeper().GetDelegation(s.providerCtx, addr, s.validator(i))
	if !found {
		s.T().Fatal("Couldn't GetDelegation")
	}
	return del.Shares.TruncateInt64()
}

func (s *PBTTestSuite) delegate(a DelegateAction) {
	psk := s.providerChain.App.GetStakingKeeper()
	pskServer := stakingkeeper.NewMsgServerImpl(psk)
	amt := sdk.NewCoin(denom, sdk.NewInt(a.amt))
	del := s.delegator()
	val := s.validator(a.val)
	msg := stakingtypes.NewMsgDelegate(del, val, amt)
	pskServer.Delegate(sdk.WrapSDKContext(s.providerCtx), msg)
}

func (s *PBTTestSuite) undelegate(a UndelegateAction) {

	psk := s.providerChain.App.GetStakingKeeper()
	pskServer := stakingkeeper.NewMsgServerImpl(psk)
	amt := sdk.NewCoin(denom, sdk.NewInt(a.amt))
	del := s.delegator()
	val := s.validator(a.val)
	msg := stakingtypes.NewMsgUndelegate(del, val, amt)
	pskServer.Undelegate(sdk.WrapSDKContext(s.providerCtx), msg)
}

func (s *PBTTestSuite) beginRedelegate(a BeginRedelegateAction) {

	psk := s.providerChain.App.GetStakingKeeper()
	pskServer := stakingkeeper.NewMsgServerImpl(psk)

	amt := sdk.NewCoin(denom, sdk.NewInt(a.amt))
	del := s.delegator()
	valSrc := s.validator(a.valSrc)
	valDst := s.validator(a.valDst)
	msg := stakingtypes.NewMsgBeginRedelegate(del, valSrc, valDst, amt)
	pskServer.BeginRedelegate(sdk.WrapSDKContext(s.providerCtx), msg)
}

func (s *PBTTestSuite) providerSlash(a ProviderSlashAction) {
	psk := s.providerChain.App.GetStakingKeeper()
	val := s.consAddr(a.val)
	h := int64(a.infractionHeight)
	power := int64(a.power)
	factor := sdk.NewDec(int64(a.slashPercentage)) // TODO: I think it's a percentage (from 100)?
	psk.Slash(s.providerCtx, val, h, power, factor)
}

func (s *PBTTestSuite) consumerSlash(a ConsumerSlashAction) {
	cccvk := s.consumerChain.App.(*appConsumer.App).ConsumerKeeper
	val := s.consAddr(a.val)
	h := int64(a.infractionHeight)
	power := int64(a.power)
	factor := sdk.NewDec(int64(a.slashPercentage)) // TODO: I think it's a percentage (from 100)?
	cccvk.Slash(s.consumerCtx, val, h, power, factor)
}

func (s *PBTTestSuite) jumpToBlock(a JumpToBlockAction) {
	h := int64(a.height)
	hCurr := s.chain(a.chain).CurrentHeader.Height
	if h <= hCurr {
		s.T().Fatal("Can only jump to future block")
	}
	dt := uint64(h - hCurr)
	s.coordinator.CommitNBlocks(s.chain(a.chain), dt)
}

func (s *PBTTestSuite) updateClient(a UpdateClientAction) {
	chain := s.chain(a.chain)
	endpoint := s.endpoint(a.chain)
	ctx := s.ctx(a.chain)

	var header exported.Header

	var err error
	switch endpoint.ClientConfig.GetClientType() {
	case exported.Tendermint:
		header, err = endpoint.Chain.ConstructUpdateTMClientHeader(endpoint.Counterparty.Chain, endpoint.ClientID)
	default:
		err = fmt.Errorf("client type %s is not supported", endpoint.ClientConfig.GetClientType())
	}

	if err != nil {
		s.T().Fatal(err)
	}

	msg, err := clienttypes.NewMsgUpdateClient(
		endpoint.ClientID, header,
		endpoint.Chain.SenderAccount.GetAddress().String(),
	)

	require.NoError(endpoint.Chain.T, err)

	_, err = chain.App.GetIBCKeeper().UpdateClient(sdk.WrapSDKContext(*ctx), msg)
	if err != nil {
		s.T().Fatal(err)
	}

}

func adjustParams(s *PBTTestSuite) {
	p := s.providerChain.App.GetStakingKeeper().GetParams(s.providerCtx)
	p.MaxValidators = maxValidators
	s.providerChain.App.GetStakingKeeper().SetParams(s.providerCtx, p)
}

func (s *PBTTestSuite) TestAssumptions() {

	adjustParams(s)

	/*
		TODO:
		1. check delegator balance (done manually)
		2. check max validators
		3. check delegations to each provider validator
		4. check validator tokens
		5. check validator status
		6. check heights on both chains
		7. check there are 4 validators
		8. do I need to check the params are the same on both chains?
	*/

	/*
		delegatorBalance() overflows int64 because it is set to a number greater than 2^63 in genesis.
		It's easiest to assume we have enough funds.
	*/

	maxValsE := uint32(3)
	maxVals := s.providerChain.App.GetStakingKeeper().GetParams(s.providerCtx).MaxValidators

	if maxValsE != maxVals {
		s.T().Fatal("Bad test")
	}

	for i := 0; i < 4; i++ {
		// This is the genesis delegation
		delE := sdk.TokensFromConsensusPower(1, sdk.DefaultPowerReduction).Int64()
		del := s.delegation(int64(i))
		if delE != del {
			s.T().Fatal("Bad test")
		}
	}

	step := sdk.TokensFromConsensusPower(100, sdk.DefaultPowerReduction).Int64()
	for i := 0; i < 4; i++ {
		s.delegate(DelegateAction{int64(i), (4 - int64(i)) * step, true})
	}

	for i := 0; i < 4; i++ {
		delE := (4-int64(i))*step + sdk.TokensFromConsensusPower(1, sdk.DefaultPowerReduction).Int64()
		del := s.delegation(int64(i))
		if delE != del {
			s.T().Fatal("Bad test")
		}
	}

	for i := 0; i < maxValidators; i++ {
		// First ones should be bonded
		A := s.validatorStatus(p, int64(i))
		E := stakingtypes.Bonded
		if E != A {
			s.T().Fatal("Bad test")
		}
	}

	for i := maxValidators; i < 4; i++ {
		// It will still be bonded because we didn't do valStateChange yet
		A := s.validatorStatus(p, int64(i))
		E := stakingtypes.Bonded
		if E != A {
			s.T().Fatal("Bad test")
		}
	}

	ph := s.providerChain.GetContext().BlockHeader().Height
	ch := s.consumerChain.GetContext().BlockHeader().Height
	if ph != ch {
		s.T().Fatal("Bad test")
	}

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
		case "updateClient":
			s.updateClient(UpdateClientAction{a.chain})
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
			kind:  "updateClient",
			chain: "provider",
		},
	}

	executeTrace(s, trace)

}
