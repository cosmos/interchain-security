package difftest_test

import (
	"encoding/json"
	"fmt"
	"io/ioutil"
	"math"
	"os"
	"strconv"
	"testing"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/stretchr/testify/suite"

	distrtypes "github.com/cosmos/cosmos-sdk/x/distribution/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channelkeeper "github.com/cosmos/ibc-go/v3/modules/core/04-channel/keeper"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	commitmenttypes "github.com/cosmos/ibc-go/v3/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"

	slashingtypes "github.com/cosmos/cosmos-sdk/x/slashing/types"
	stakingkeeper "github.com/cosmos/cosmos-sdk/x/staking/keeper"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	appProvider "github.com/cosmos/interchain-security/app/provider"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	"github.com/cosmos/interchain-security/x/ccv/types"

	tmtypes "github.com/tendermint/tendermint/types"

	difftest "github.com/cosmos/interchain-security/x/ccv/difftest"
	abci "github.com/tendermint/tendermint/abci/types"

	tmproto "github.com/tendermint/tendermint/proto/tendermint/types"

	"github.com/cosmos/ibc-go/v3/testing/mock"
)

const P = "provider"
const C = "consumer"

// Height is offset from model to due to bootstrappingG
const MODEL_HEIGHT_OFFSET = int64(18)

// TODO: do I need different denoms for each chain?
const DENOM = sdk.DefaultBondDenom

var SLASH_DOUBLESIGN = slashingtypes.DefaultSlashFractionDoubleSign
var SLASH_DOWNTIME = slashingtypes.DefaultSlashFractionDowntime

func init() {
	// Tokens = Power
	sdk.DefaultPowerReduction = sdk.NewInt(1)
	SLASH_DOUBLESIGN = sdk.NewDec(1).Quo(sdk.NewDec(2))
	SLASH_DOWNTIME = sdk.NewDec(1).Quo(sdk.NewDec(4))
}

type Ack struct {
	ack     []byte
	packet  channeltypes.Packet
	commits int
}

type PBTTestSuite struct {
	suite.Suite

	coordinator *ibctesting.Coordinator

	// testing chains
	providerChain *ibctesting.TestChain
	consumerChain *ibctesting.TestChain

	path *ibctesting.Path

	mustBeginBlock map[string]bool

	valAddresses []sdk.ValAddress

	outbox map[string][]channeltypes.Packet
	acks   map[string][]Ack

	heightLastClientUpdate map[string]int64
}

func TestPBTTestSuite(t *testing.T) {
	suite.Run(t, new(PBTTestSuite))
}

func (s *PBTTestSuite) addAck(receiver string, ack []byte, packet channeltypes.Packet) {
	s.acks[receiver] = append(s.acks[receiver], Ack{ack, packet, 0})
}

func (s *PBTTestSuite) commitAcks(committer string) {
	for _, ack := range s.acks[s.other(committer)] {
		ack.commits += 1
	}
}

func (s *PBTTestSuite) createValidator() (tmtypes.PrivValidator, sdk.ValAddress) {
	privVal := mock.NewPV()
	pubKey, err := privVal.GetPubKey()
	s.Require().NoError(err)
	// TODO: figure if need to do something with signersByAddress
	// (see NewPBTTestChain)
	val := tmtypes.NewValidator(pubKey, 0)
	addr, err := sdk.ValAddressFromHex(val.Address.String())
	s.Require().NoError(err)
	PK := privVal.PrivKey.PubKey()

	coin := sdk.NewCoin(DENOM, sdk.NewInt(0))
	msg, err := stakingtypes.NewMsgCreateValidator(addr, PK, coin, stakingtypes.Description{}, stakingtypes.NewCommissionRates(sdk.ZeroDec(), sdk.ZeroDec(), sdk.ZeroDec()), sdk.ZeroInt())
	s.Require().NoError(err)
	psk := s.providerChain.App.GetStakingKeeper()
	pskServer := stakingkeeper.NewMsgServerImpl(psk)
	pskServer.CreateValidator(sdk.WrapSDKContext(s.ctx(P)), msg)
	return privVal, addr
}

func (s *PBTTestSuite) specialDelegate(del int, val sdk.ValAddress, x int) {
	psk := s.providerChain.App.GetStakingKeeper()
	pskServer := stakingkeeper.NewMsgServerImpl(psk)
	amt := sdk.NewCoin(DENOM, sdk.NewInt(int64(x)))
	d := s.providerChain.SenderAccounts[del].SenderAccount.GetAddress()
	msg := stakingtypes.NewMsgDelegate(d, val, amt)
	pskServer.Delegate(sdk.WrapSDKContext(s.ctx(P)), msg)
}

func (s *PBTTestSuite) SetupTest() {

	s.coordinator, s.providerChain, s.consumerChain, s.valAddresses = difftest.NewDTProviderConsumerCoordinator(s.T())
	s.mustBeginBlock = map[string]bool{P: true, C: true}
	s.outbox = map[string][]channeltypes.Packet{P: {}, C: {}}
	s.acks = map[string][]Ack{P: {}, C: {}}
	s.heightLastClientUpdate = map[string]int64{P: 0, C: 0}

	// Add two more validator
	// Only added two in chain creation
	// TODO: clean up this horrible mess
	// see this for reasoning https://github.com/danwt/informal-cosmos-hub-team/issues/13#issuecomment-1139704176
	// TODO: the hacks here do seem to solve the problem
	// temporarily!
	val2, val2addr := s.createValidator()
	val3, val3addr := s.createValidator()
	val2pk, err := val2.GetPubKey()
	s.Require().Nil(err)
	val3pk, err := val3.GetPubKey()
	s.Require().Nil(err)
	s.valAddresses = append(s.valAddresses, val2addr)
	s.valAddresses = append(s.valAddresses, val3addr)
	// TODO: if this addr way doesn't work try using same way as in
	// NewPBTTestChain
	s.providerChain.Signers[val2pk.Address().String()] = val2
	s.providerChain.Signers[val3pk.Address().String()] = val3
	s.consumerChain.Signers[val2pk.Address().String()] = val2
	s.consumerChain.Signers[val3pk.Address().String()] = val3

	// TODO: delete this once it is no longer needed
	s.DisableConsumerDistribution()

	tmConfig := ibctesting.NewTendermintConfig()

	// commit a block on provider chain before creating client
	s.coordinator.CommitBlock(s.providerChain)

	// create client and consensus state of provider chain to initialize consumer chain genesis.
	height := s.providerChain.LastHeader.GetHeight().(clienttypes.Height)
	UpgradePath := []string{"upgrade", "upgradedIBCState"}

	tmConfig.UnbondingPeriod = difftest.UNBONDING
	tmConfig.TrustingPeriod = difftest.TRUSTING
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

	cfg := s.path.EndpointB.ClientConfig.(*ibctesting.TendermintConfig)
	cfg.UnbondingPeriod = difftest.UNBONDING
	cfg.TrustingPeriod = difftest.TRUSTING
	s.path.EndpointB.CreateClient()

	s.providerChain.App.(*appProvider.App).ProviderKeeper.SetConsumerClient(s.ctx(P), s.consumerChain.ChainID, s.path.EndpointB.ClientID)

	// TODO: I added this section, should I remove it or move it?
	//~~~~~~~~~~
	s.coordinator.CreateConnections(s.path)

	// CCV channel handshake will automatically initiate transfer channel handshake on ACK
	// so transfer channel will be on stage INIT when CreateChannels for ccv path returns.
	s.coordinator.CreateChannels(s.path)
	//~~~~~~~~~~

	s.jumpNBlocks(JumpNBlocks{[]string{P}, 1, 1})
	// TODO: Is it correct to catch the consumer up with the provider here?
	s.jumpNBlocks(JumpNBlocks{[]string{C}, 2, 1})

	s.idempotentBeginBlock(P)
	s.idempotentBeginBlock(C)

	s.specialDelegate(1, s.validator(2), 1*difftest.TOKEN_SCALAR)
	s.specialDelegate(1, s.validator(3), 1*difftest.TOKEN_SCALAR)
	s.specialDelegate(0, s.validator(2), 2*difftest.TOKEN_SCALAR)
	s.specialDelegate(0, s.validator(3), 1*difftest.TOKEN_SCALAR)

	sparams := s.providerChain.App.(*appProvider.App).SlashingKeeper.GetParams(s.ctx(P))
	sparams.SlashFractionDoubleSign = SLASH_DOUBLESIGN
	sparams.SlashFractionDowntime = SLASH_DOWNTIME
	s.providerChain.App.(*appProvider.App).SlashingKeeper.SetParams(s.ctx(P), sparams)

	s.jumpNBlocks(JumpNBlocks{[]string{P, C}, 1, 5})

	s.idempotentBeginBlock(P)
	s.idempotentBeginBlock(C)

}

/*
~~~~~~~~~~~~
QUERIES
~~~~~~~~~~~~
*/

func (s *PBTTestSuite) ctx(chain string) sdk.Context {
	return s.chain(chain).GetContext()
}

func (s *PBTTestSuite) chain(chain string) *ibctesting.TestChain {
	return map[string]*ibctesting.TestChain{P: s.providerChain, C: s.consumerChain}[chain]
}

func (s *PBTTestSuite) other(chain string) string {
	return map[string]string{P: C, C: P}[chain]
}

func (s *PBTTestSuite) height(chain string) int64 {
	return s.chain(chain).CurrentHeader.GetHeight()
}

func (s *PBTTestSuite) time(chain string) time.Time {
	return s.chain(chain).CurrentHeader.Time
}

func (s *PBTTestSuite) globalTime() time.Time {
	return s.coordinator.CurrentTime
}

func (s *PBTTestSuite) endpoint(chain string) *ibctesting.Endpoint {
	return map[string]*ibctesting.Endpoint{P: s.path.EndpointB, C: s.path.EndpointA}[chain]
}

func (s *PBTTestSuite) delegator() sdk.AccAddress {
	return s.providerChain.SenderAccount.GetAddress()
}

func (s *PBTTestSuite) validator(i int64) sdk.ValAddress {
	return s.valAddresses[i]
}

func (s *PBTTestSuite) consAddr(i int64) sdk.ConsAddress {
	return sdk.ConsAddress(s.validator(i))
}

func (s *PBTTestSuite) isJailed(i int64) bool {
	sk := s.chain(P).App.GetStakingKeeper()
	val, found := sk.GetValidator(s.ctx(P), s.validator(i))
	if !found {
		s.T().Fatal("Couldn't GetValidator")
	}
	return val.IsJailed()
}

func (s *PBTTestSuite) consumerPower(i int64) (int64, error) {
	// TODO: I need to use consumer chain cast to get then
	// call GetCCValidator.Power
	ck := s.consumerChain.App.(*appConsumer.App).ConsumerKeeper
	val, found := ck.GetCCValidator(s.ctx(C), s.validator(i))
	if !found {
		return 0, fmt.Errorf("CCValidator not found")
	}
	return val.Power, nil
}

func (s *PBTTestSuite) delegation(i int64) int64 {
	addr := s.delegator()
	del, found := s.providerChain.App.GetStakingKeeper().GetDelegation(s.ctx(P), addr, s.validator(i))
	if !found {
		s.T().Fatal("Couldn't GetDelegation")
	}
	return del.Shares.TruncateInt64()
}

func (s *PBTTestSuite) validatorStatus(chain string, i int64) stakingtypes.BondStatus {
	val, found := s.chain(chain).App.GetStakingKeeper().GetValidator(s.ctx(chain), s.validator(i))
	if !found {
		s.T().Fatal("Couldn't GetValidator")
	}
	return val.GetStatus()
}

func (s *PBTTestSuite) providerTokens(i int64) int64 {
	addr := s.validator(i)
	val, found := s.chain(P).App.GetStakingKeeper().GetValidator(s.ctx(P), addr)
	if !found {
		s.T().Fatal("Couldn't GetValidator")
	}
	return val.Tokens.Int64()
}

func (s *PBTTestSuite) delegatorBalance() int64 {
	del := s.delegator()
	app := s.providerChain.App.(*appProvider.App)
	bal := app.BankKeeper.GetBalance(s.ctx(P), del, DENOM)
	return bal.Amount.Int64()
}

/*
~~~~~~~~~~~~
MODEL
~~~~~~~~~~~~
*/

type Delegate struct {
	val int64
	amt int64
}
type Undelegate struct {
	val int64
	amt int64
}
type JumpNBlocks struct {
	chains          []string
	n               int64
	secondsPerBlock int64
}
type Deliver struct {
	chain string
}
type ProviderSlash struct {
	val    int64
	power  int64
	height int64
	factor sdk.Dec
}
type ConsumerSlash struct {
	val        int64
	height     int64
	power      int64
	isDowntime bool
}

func (s *PBTTestSuite) beginBlock(chain string) {

	c := s.chain(chain)

	// increment the current header
	c.CurrentHeader = tmproto.Header{
		ChainID:            c.ChainID,
		Height:             c.App.LastBlockHeight() + 1,
		AppHash:            c.App.LastCommitID().Hash,
		Time:               s.coordinator.CurrentTime,
		ValidatorsHash:     c.Vals.Hash(),
		NextValidatorsHash: c.NextVals.Hash(),
	}

	_ = c.App.BeginBlock(abci.RequestBeginBlock{Header: c.CurrentHeader})

}

func (s *PBTTestSuite) idempotentBeginBlock(chain string) {
	if s.mustBeginBlock[chain] {
		s.mustBeginBlock[chain] = false
		s.beginBlock(chain)
		s.idempotentUpdateClient(chain)
	}
}

func (s *PBTTestSuite) idempotentDeliverAcks(receiver string) error {
	acks := s.acks[receiver]
	replacement := []Ack{}
	for _, ack := range acks {
		if 2 <= ack.commits {
			// s.idempotentUpdateClient(receiver)
			// p := ack.packet
			// difftest.TryRelayAck(s.endpoint(s.other(receiver)), s.endpoint(receiver), p, ack.ack)
		} else {
			replacement = append(replacement, ack)
		}
	}
	s.acks[receiver] = replacement

	return nil
}

func (s PBTTestSuite) idempotentUpdateClient(chain string) {
	otherHeight := s.height(s.other(chain))
	if otherHeight < int64(s.heightLastClientUpdate[chain]) {
		err := difftest.UpdateReceiverClient(s.endpoint(s.other(chain)), s.endpoint(chain))
		if err != nil {
			s.FailNow("Bad test")
		}
		s.heightLastClientUpdate[chain] = otherHeight
	}

}

func (s *PBTTestSuite) delegate(a Delegate) {
	s.idempotentBeginBlock(P)
	s.idempotentDeliverAcks(P)
	psk := s.providerChain.App.GetStakingKeeper()
	pskServer := stakingkeeper.NewMsgServerImpl(psk)
	amt := sdk.NewCoin(DENOM, sdk.NewInt(a.amt))
	del := s.delegator()
	val := s.validator(a.val)
	msg := stakingtypes.NewMsgDelegate(del, val, amt)
	pskServer.Delegate(sdk.WrapSDKContext(s.ctx(P)), msg)
}

func (s *PBTTestSuite) undelegate(a Undelegate) {
	s.idempotentBeginBlock(P)
	s.idempotentDeliverAcks(P)
	psk := s.providerChain.App.GetStakingKeeper()
	pskServer := stakingkeeper.NewMsgServerImpl(psk)
	amt := sdk.NewCoin(DENOM, sdk.NewInt(a.amt))
	del := s.delegator()
	val := s.validator(a.val)
	msg := stakingtypes.NewMsgUndelegate(del, val, amt)
	pskServer.Undelegate(sdk.WrapSDKContext(s.ctx(P)), msg)
}

func (s *PBTTestSuite) hackBeginBlock(chain string) {
	c := s.chain(chain)

	dt := 5
	newT := s.coordinator.CurrentTime.Add(time.Second * time.Duration(dt)).UTC()

	// increment the current header
	c.CurrentHeader = tmproto.Header{
		ChainID:            c.ChainID,
		Height:             c.App.LastBlockHeight() + 1,
		AppHash:            c.App.LastCommitID().Hash,
		Time:               newT,
		ValidatorsHash:     c.Vals.Hash(),
		NextValidatorsHash: c.NextVals.Hash(),
	}

	c.App.BeginBlock(abci.RequestBeginBlock{Header: c.CurrentHeader})
}

func (s *PBTTestSuite) endBlock(chain string) {

	s.idempotentBeginBlock(chain)
	s.idempotentDeliverAcks(chain)

	c := s.chain(chain)

	ebRes := c.App.EndBlock(abci.RequestEndBlock{Height: c.CurrentHeader.Height})

	c.App.Commit()

	c.LastHeader = c.CurrentTMClientHeader()

	c.NextVals = ibctesting.ApplyValSetChanges(c.T, c.Vals, ebRes.ValidatorUpdates)

	s.mustBeginBlock[chain] = true

	for _, e := range ebRes.Events {
		if e.Type == channeltypes.EventTypeSendPacket {
			packet, err := channelkeeper.ReconstructPacketFromEvent(e)
			s.Require().NoError(err)
			s.outbox[chain] = append(s.outbox[chain], packet)
		}
	}

	s.commitAcks(chain)

	/*
		This is a hack!!!
		See https://github.com/cosmos/interchain-security/issues/127
		In short:
			1. needed to access .GetContext()
			2. Dangerous, non idempotent, leads to different contexts
		TODO: Must be removed!
	*/
	s.hackBeginBlock(chain)

}

func (s *PBTTestSuite) increaseSeconds(seconds int64) {
	s.coordinator.CurrentTime = s.coordinator.CurrentTime.Add(time.Second * time.Duration(seconds)).UTC()
}

func (s *PBTTestSuite) jumpNBlocks(a JumpNBlocks) {
	for i := int64(0); i < a.n; i++ {
		for _, c := range a.chains {
			s.endBlock(c)
			fmt.Println("endBlock", c)
		}
		s.increaseSeconds(a.secondsPerBlock)
	}
}

func (s *PBTTestSuite) deliver(a Deliver) {
	s.idempotentBeginBlock(a.chain)
	s.idempotentDeliverAcks(a.chain)
	other := map[string]string{P: C, C: P}[a.chain]
	fmt.Println("outbox size ", len(s.outbox[other]))
	for _, p := range s.outbox[other] {
		receiver := s.endpoint(a.chain)
		sender := receiver.Counterparty
		s.idempotentUpdateClient(a.chain)
		ack, err := difftest.TryRecvPacket(sender, receiver, p)
		if err != nil {
			s.FailNow("Relay failed", err)
		}
		fmt.Println("Done TryRelay without err")
		s.addAck(s.other(a.chain), ack, p)
	}
	s.outbox[other] = []channeltypes.Packet{}
}

func (s *PBTTestSuite) providerSlash(a ProviderSlash) {
	s.idempotentBeginBlock(P)
	s.idempotentDeliverAcks(P)
	psk := s.providerChain.App.GetStakingKeeper()
	val := s.consAddr(a.val)
	h := int64(a.height)
	h += MODEL_HEIGHT_OFFSET
	power := int64(a.power)
	factor := a.factor
	psk.Slash(s.ctx(P), val, h, power, factor, -1) // TODO: check params here!
}

func (s *PBTTestSuite) consumerSlash(a ConsumerSlash) {
	s.idempotentBeginBlock(C)
	s.idempotentDeliverAcks(C)
	cccvk := s.consumerChain.App.(*appConsumer.App).ConsumerKeeper
	val := s.consAddr(a.val)
	h := int64(a.height)
	h += MODEL_HEIGHT_OFFSET
	power := int64(a.power)
	kind := stakingtypes.Downtime
	if !a.isDowntime {
		kind = stakingtypes.DoubleSign
	}
	cccvk.Slash(s.ctx(C), val, h, power, sdk.Dec{}, kind) // TODO: check params here!
}

/*
~~~~~~~~~~~~
ASSUMPTIONS TEST
~~~~~~~~~~~~
*/

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

func (s *PBTTestSuite) TestAssumptions() {
	s.Require().Equal(SLASH_DOWNTIME, s.providerChain.App.(*appProvider.App).SlashingKeeper.SlashFractionDowntime(s.ctx(P)))
	s.Require().Equal(SLASH_DOUBLESIGN, s.providerChain.App.(*appProvider.App).SlashingKeeper.SlashFractionDoubleSign(s.ctx(P)))

	s.Require().Equal(false, s.mustBeginBlock[P])
	s.Require().Equal(false, s.mustBeginBlock[C])

	/*
		Adding a 1 is needed here because the first step of any model execution
		is to increase the height by 1.
		Here this step is missing, so we account for it.
	*/
	s.Require().Equal(0+1+MODEL_HEIGHT_OFFSET, s.height(P))
	s.Require().Equal(0+1+MODEL_HEIGHT_OFFSET, s.height(C))

	s.Require().Empty(s.outbox[P])
	s.Require().Empty(s.outbox[C])

	s.Require().Equal(int64(1577923353), s.time(P).Unix())
	s.Require().Equal(int64(1577923353), s.time(C).Unix())
	s.Require().Equal(int64(1577923353), s.globalTime().Unix())

	s.Require().Equal(int64(1000000000000000), s.delegatorBalance())

	maxValsE := uint32(2)
	maxVals := s.providerChain.App.GetStakingKeeper().GetParams(s.ctx(P)).MaxValidators

	if maxValsE != maxVals {
		s.T().Fatal("Bad test")
	}

	initialModelState := difftest.InitialModelState{
		Delegation: []int64{4 * difftest.TOKEN_SCALAR, 3 * difftest.TOKEN_SCALAR, 2 * difftest.TOKEN_SCALAR, 1 * difftest.TOKEN_SCALAR},
		Status:     []stakingtypes.BondStatus{stakingtypes.Bonded, stakingtypes.Bonded, stakingtypes.Unbonded, stakingtypes.Unbonded},
	}

	for i := 0; i < 4; i++ {
		E := initialModelState.Delegation[i]
		A := s.delegation(int64(i))
		if E != A {
			s.T().Fatal("Bad test")
		}
	}
	for i := 0; i < 4; i++ {
		E := initialModelState.Delegation[i] + difftest.TOKEN_SCALAR
		A := s.providerTokens(int64(i))
		if E != A {
			s.T().Fatal("Bad test")
		}
	}
	for i := 0; i < 4; i++ {
		E := initialModelState.Status[i]
		A := s.validatorStatus(P, int64(i))
		if E != A {
			s.T().Fatal("Bad test")
		}
	}

	sk := s.providerChain.App.GetStakingKeeper()

	sk.IterateUnbondingDelegations(s.ctx(P),
		func(index int64, ubd stakingtypes.UnbondingDelegation) bool {
			s.T().Fatal("Bad test")
			return false // Don't stop
		})

	sk.IterateRedelegations(s.ctx(P),
		func(index int64, ubd stakingtypes.Redelegation) bool {
			s.T().Fatal("Bad test")
			return false // Don't stop
		})

	endTime := time.Unix(math.MaxInt64, 0)
	endHeight := int64(math.MaxInt64) // is this borked?
	// TODO: these are supposed to be MAX and not MIN right?
	unbondingValIterator := sk.ValidatorQueueIterator(s.ctx(P), endTime, endHeight)
	defer unbondingValIterator.Close()
	for ; unbondingValIterator.Valid(); unbondingValIterator.Next() {
		s.T().Fatal("Bad test")
	}

	eFound := []bool{true, true, false, false}
	ePower := []int64{5 * difftest.TOKEN_SCALAR, 4 * difftest.TOKEN_SCALAR}

	ck := s.consumerChain.App.(*appConsumer.App).ConsumerKeeper

	for i := 0; i < 4; i++ {
		addr := s.validator(int64(i))
		val, found := ck.GetCCValidator(s.ctx(C), addr)
		s.Require().Equal(eFound[i], found)
		if eFound[i] {
			if ePower[i] != val.Power {
				s.T().Fatal("Bad test")
			}
		}
	}

	s.Require().Empty(ck.GetPendingSlashRequests(s.ctx(C)))

	ck.IterateUnbondingPacket(s.ctx(C),
		func(seq uint64, packet channeltypes.Packet) bool {
			s.T().Fatal("Bad test")
			return false // Don't stop
		})

	ck.IterateUnbondingTime(s.ctx(C),
		func(seq uint64, timeNs uint64) bool {
			s.T().Fatal("Bad test")
			return false // Don't stop
		})

	s.T().Fatal("Good test! (Sanity check)")
}

/*
~~~~~~~~~~~~
TRACE TEST
~~~~~~~~~~~~
*/

func (s *PBTTestSuite) matchState(chain string, trace difftest.Trace, i int) {
	c := trace.Consequences[i]

	implementationStartTime := time.Unix(1577923353, 0).UTC()
	modelOffset := time.Second * time.Duration(-5)
	timeOffset := implementationStartTime.Add(modelOffset)

	if chain == P {
		s.Require().Equal(int64(c.H.Provider+int(MODEL_HEIGHT_OFFSET)), s.height(P), i)
		s.Require().Equal(int64(c.DelegatorTokens), s.delegatorBalance())
		// TODO: unhardcode this and check that it's correct
		for j, jailedUntilTimestamp := range c.Jailed {
			// TODO: tidy up
			// the type/meaning of jailed is confusing here
			isJailed := false
			if jailedUntilTimestamp != nil {
				isJailed = true
			}
			s.Require().Equal(isJailed, s.isJailed(int64(j)))
		}
		t := time.Second * time.Duration(c.T.Provider)
		s.Require().Equal(timeOffset.Add(t), s.time(P))
		for j, tokens := range c.Tokens {
			s.Require().Equal(int64(tokens), s.providerTokens(int64(j)))
		}
	}
	if chain == C {
		s.Require().Equal(int64(c.H.Consumer+int(MODEL_HEIGHT_OFFSET)), s.height(C), i)
		for j, power := range c.Power {
			actual, err := s.consumerPower(int64(j))
			if power != nil {
				s.Require().Nil(err)
				s.Require().Equal(int64(*power), actual)
			} else {
				s.Require().Error(err)
			}
		}
		t := time.Second * time.Duration(c.T.Consumer)
		s.Require().Equal(timeOffset.Add(t), s.time(C))
	}
}

func executeTrace(s *PBTTestSuite, trace difftest.Trace) {

	/*
		There is a limitation: you can't query using .ctx after a block
		has been committed. So limit querying to happen only after a block
		has begun but not been committed. The last step in JumpNBlocks is
		always a commit so you can't match the state afterwards.
	*/
	for i, a := range trace.Actions {
		fmt.Println("Action ", i, ", kind: ", a.Kind)
		switch a.Kind {
		case "Delegate":
			s.delegate(Delegate{
				int64(a.Val),
				int64(a.Amt),
			})
			s.matchState(P, trace, i)
		case "Undelegate":
			s.undelegate(Undelegate{
				int64(a.Val),
				int64(a.Amt),
			})
			s.matchState(P, trace, i)
		case "JumpNBlocks":
			s.jumpNBlocks(JumpNBlocks{
				a.Chains,
				int64(a.N),
				int64(a.SecondsPerBlock),
			})
		case "Deliver":
			s.deliver(Deliver{a.Chain})
			s.matchState(a.Chain, trace, i)
		case "ProviderSlash":
			factor := strconv.FormatFloat(a.Factor, 'f', 3, 64)
			s.providerSlash(ProviderSlash{
				int64(a.Val),
				int64(a.Power),
				int64(a.Height),
				sdk.MustNewDecFromStr(factor),
			})
			s.matchState(P, trace, i)
		case "ConsumerSlash":
			s.consumerSlash(ConsumerSlash{
				int64(a.Val),
				int64(a.Height),
				int64(a.Power),
				a.IsDowntime,
			})
			s.matchState(C, trace, i)
		default:
			s.Require().FailNow("Couldn't parse action")
		}
	}
}

func loadTraces(fn string) []difftest.Trace {

	fd, err := os.Open(fn)

	if err != nil {
		panic(err)
	}

	defer fd.Close()

	byteValue, _ := ioutil.ReadAll(fd)

	var ret []difftest.Trace

	err = json.Unmarshal([]byte(byteValue), &ret)

	if err != nil {
		panic(err)
	}

	return ret
}

func executeTraces(s *PBTTestSuite, traces []difftest.Trace) {
	for i, trace := range traces {
		fmt.Println("Executing trace ", i)
		executeTrace(s, trace)
	}
}

func (s *PBTTestSuite) TestTracesCovering() {
	executeTraces(s, loadTraces("traces_covering.json"))
}
