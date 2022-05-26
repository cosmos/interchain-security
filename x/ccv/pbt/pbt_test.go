package pbt_test

import (
	"encoding/json"
	"io/ioutil"
	"math"
	"os"
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

	host "github.com/cosmos/ibc-go/v3/modules/core/24-host"

	stakingkeeper "github.com/cosmos/cosmos-sdk/x/staking/keeper"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	appProvider "github.com/cosmos/interchain-security/app/provider"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	"github.com/cosmos/interchain-security/x/ccv/types"

	tmtypes "github.com/tendermint/tendermint/types"

	pbt "github.com/cosmos/interchain-security/x/ccv/pbt"
	abci "github.com/tendermint/tendermint/abci/types"

	tmproto "github.com/tendermint/tendermint/proto/tendermint/types"

	"github.com/cosmos/ibc-go/v3/testing/mock"
	"github.com/cosmos/ibc-go/v3/testing/simapp"
)

const P = "provider"
const C = "consumer"

// TODO: do I need different denoms for each chain?
const denom = sdk.DefaultBondDenom

func init() {
	// Tokens = Power
	sdk.DefaultPowerReduction = sdk.NewInt(1)
}

type Ack struct {
	ack       []byte
	packet    channeltypes.Packet
	committed bool
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
}

func TestPBTTestSuite(t *testing.T) {
	suite.Run(t, new(PBTTestSuite))
}

func (s *PBTTestSuite) addAck(receiver string, ack []byte, packet channeltypes.Packet) {
	s.acks[receiver] = append(s.acks[receiver], Ack{ack, packet, false})
}

func (s *PBTTestSuite) commitAcks(committer string) {
	for _, ack := range s.acks[s.other(committer)] {
		ack.committed = true
	}
}

func (s *PBTTestSuite) createValidator() sdk.ValAddress {
	privVal := mock.NewPV()
	pubKey, err := privVal.GetPubKey()
	s.Require().NoError(err)
	// TODO: figure if need to do something with signersByAddress
	// (see NewPBTTestChain)
	val := tmtypes.NewValidator(pubKey, 0)
	addr, err := sdk.ValAddressFromHex(val.Address.String())
	s.Require().NoError(err)
	PK := privVal.PrivKey.PubKey()

	coin := sdk.NewCoin(denom, sdk.NewInt(0))
	msg, err := stakingtypes.NewMsgCreateValidator(addr, PK, coin, stakingtypes.Description{}, stakingtypes.NewCommissionRates(sdk.ZeroDec(), sdk.ZeroDec(), sdk.ZeroDec()), sdk.ZeroInt())
	s.Require().NoError(err)
	psk := s.providerChain.App.GetStakingKeeper()
	pskServer := stakingkeeper.NewMsgServerImpl(psk)
	pskServer.CreateValidator(sdk.WrapSDKContext(s.ctx(P)), msg)
	return addr
}

func (s *PBTTestSuite) specialDelegate(del int, val sdk.ValAddress, x int) {
	psk := s.providerChain.App.GetStakingKeeper()
	pskServer := stakingkeeper.NewMsgServerImpl(psk)
	amt := sdk.NewCoin(denom, sdk.NewInt(int64(x)))
	d := s.providerChain.SenderAccounts[del].SenderAccount.GetAddress()
	msg := stakingtypes.NewMsgDelegate(d, val, amt)
	pskServer.Delegate(sdk.WrapSDKContext(s.ctx(P)), msg)
}

func (s *PBTTestSuite) SetupTest() {

	s.coordinator, s.providerChain, s.consumerChain, s.valAddresses = pbt.NewPBTProviderConsumerCoordinator(s.T())
	s.mustBeginBlock = map[string]bool{P: true, C: true}
	s.outbox = map[string][]channeltypes.Packet{P: {}, C: {}}
	s.acks = map[string][]Ack{P: {}, C: {}}

	// Add two more validator
	// Only added two in chain creation
	s.valAddresses = append(s.valAddresses, s.createValidator())
	s.valAddresses = append(s.valAddresses, s.createValidator())

	// TODO: needed?
	s.DisableConsumerDistribution()

	tmConfig := ibctesting.NewTendermintConfig()

	// commit a block on provider chain before creating client
	s.coordinator.CommitBlock(s.providerChain)

	// create client and consensus state of provider chain to initialize consumer chain genesis.
	height := s.providerChain.LastHeader.GetHeight().(clienttypes.Height)
	UpgradePath := []string{"upgrade", "upgradedIBCState"}

	// tmConfig.UnbondingPeriod = 5 * time.Second
	// tmConfig.TrustingPeriod = 4 * time.Second
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

	s.jumpNBlocks(JumpNBlocks{[]string{P}, 1, 5})
	// TODO: Is it correct to catch the consumer up with the provider here?
	s.jumpNBlocks(JumpNBlocks{[]string{C}, 2, 5})

	s.idempotentBeginBlock(P)
	s.idempotentBeginBlock(C)

	s.specialDelegate(1, s.validator(2), 1)
	s.specialDelegate(1, s.validator(3), 1)
	s.specialDelegate(0, s.validator(2), 2)
	s.specialDelegate(0, s.validator(3), 1)

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

func (s *PBTTestSuite) validatorStatus(chain string, i int64) stakingtypes.BondStatus {
	val, found := s.chain(chain).App.GetStakingKeeper().GetValidator(s.ctx(chain), s.validator(i))
	if !found {
		s.T().Fatal("Couldn't GetValidator")
	}
	return val.GetStatus()
}

func (s *PBTTestSuite) delegatorBalance() int64 {
	del := s.delegator()
	app := s.providerChain.App.(*appProvider.App)
	bal := app.BankKeeper.GetBalance(s.ctx(P), del, denom)
	return bal.Amount.Int64()
}

func (s *PBTTestSuite) validatorTokens(chain string, i int64) int64 {
	addr := s.validator(i)
	val, found := s.chain(chain).App.GetStakingKeeper().GetValidator(s.ctx(chain), addr)
	if !found {
		s.T().Fatal("Couldn't GetValidator")
	}
	return val.Tokens.Int64()
}

func (s *PBTTestSuite) delegation(i int64) int64 {
	addr := s.delegator()
	del, found := s.providerChain.App.GetStakingKeeper().GetDelegation(s.ctx(P), addr, s.validator(i))
	if !found {
		s.T().Fatal("Couldn't GetDelegation")
	}
	return del.Shares.TruncateInt64()
}

/*
~~~~~~~~~~~~
MODEL
~~~~~~~~~~~~
*/

type Action struct {
	Amt             int      `json:"amt,omitempty"`
	Chain           string   `json:"chain,omitempty"`
	Chains          []string `json:"chains,omitempty"`
	Factor          float64  `json:"factor,omitempty"`
	Height          int      `json:"height,omitempty"`
	IsDowntime      bool     `json:"is_downtime,omitempty"`
	Kind            string   `json:"kind"`
	N               int      `json:"n,omitempty"`
	Power           int      `json:"power,omitempty"`
	SecondsPerBlock int      `json:"seconds_per_block,omitempty"`
	Val             int      `json:"val,omitempty"`
}

type Trace struct {
	Actions []Action `json:"actions"`
}

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
	factor int64
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
	}
}

func (s *PBTTestSuite) idempotentDeliverAcks(receiver string) error {
	acks := s.acks[receiver]
	replacement := []Ack{}
	for _, ack := range acks {
		if ack.committed {
			p := ack.packet

			packetKey := host.PacketAcknowledgementKey(p.GetDestPort(), p.GetDestChannel(), p.GetSequence())
			proof, proofHeight := s.endpoint(s.other(receiver)).QueryProof(packetKey)

			ackMsg := channeltypes.NewMsgAcknowledgement(p, ack.ack, proof, proofHeight, s.chain(receiver).SenderAccount.GetAddress().String())

			_, _, err := simapp.SignAndDeliver(
				s.chain(receiver).T,
				s.chain(receiver).TxConfig,
				s.chain(receiver).App.GetBaseApp(),
				s.chain(receiver).GetContext().BlockHeader(),
				[]sdk.Msg{ackMsg},
				s.chain(receiver).ChainID,
				[]uint64{s.chain(receiver).SenderAccount.GetAccountNumber()},
				[]uint64{s.chain(receiver).SenderAccount.GetSequence()},
				true, true, s.chain(receiver).SenderPrivKey,
			)
			if err != nil {
				return err
			}

			// TODO: there was a receiver.NextBlock here...

			s.chain(receiver).SenderAccount.SetSequence(s.chain(receiver).SenderAccount.GetSequence() + 1)
		} else {
			replacement = append(replacement, ack)
		}
	}
	s.acks[receiver] = replacement

	return nil
}

func (s *PBTTestSuite) delegate(a Delegate) {
	s.idempotentBeginBlock(P)
	s.idempotentDeliverAcks(P)
	psk := s.providerChain.App.GetStakingKeeper()
	pskServer := stakingkeeper.NewMsgServerImpl(psk)
	amt := sdk.NewCoin(denom, sdk.NewInt(a.amt))
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
	amt := sdk.NewCoin(denom, sdk.NewInt(a.amt))
	del := s.delegator()
	val := s.validator(a.val)
	msg := stakingtypes.NewMsgUndelegate(del, val, amt)
	pskServer.Undelegate(sdk.WrapSDKContext(s.ctx(P)), msg)
}

func (s *PBTTestSuite) endBlock(chain string) {

	s.idempotentBeginBlock(chain)
	s.idempotentDeliverAcks(chain)

	c := s.chain(chain)

	ebRes := c.App.EndBlock(abci.RequestEndBlock{Height: c.CurrentHeader.Height})
	_ = c.App.Commit()

	// set the last header to the current header
	// use nil trusted fields
	c.LastHeader = c.CurrentTMClientHeader()

	// val set changes returned from previous block get applied to the next validators
	// of this block. See tendermint spec for details.
	c.Vals = c.NextVals
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
}

func (s *PBTTestSuite) increaseSeconds(seconds int64) {
	s.coordinator.CurrentTime = s.coordinator.CurrentTime.Add(time.Second * time.Duration(seconds)).UTC()
}

func (s *PBTTestSuite) jumpNBlocks(a JumpNBlocks) {
	for i := int64(0); i < a.n; i++ {
		for _, c := range a.chains {
			s.endBlock(c)
		}
		s.increaseSeconds(a.secondsPerBlock)
	}
}

func (s *PBTTestSuite) deliver(a Deliver) {
	s.idempotentBeginBlock(a.chain)
	s.idempotentDeliverAcks(a.chain)
	other := map[string]string{P: C, C: P}[a.chain]
	for _, p := range s.outbox[other] {
		// TODO: relay! but don't use usual relay function...
		receiver := s.endpoint(a.chain)
		sender := receiver.Counterparty
		ack, err := pbt.TryRelay(sender, receiver, p)
		if err != nil {
			s.FailNow("Relay failed")
		}
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
	power := int64(a.power)
	factor := sdk.NewDec(int64(a.factor))
	psk.Slash(s.ctx(P), val, h, power, factor, -1) // TODO: check params here!
}

func (s *PBTTestSuite) consumerSlash(a ConsumerSlash) {
	s.idempotentBeginBlock(C)
	s.idempotentDeliverAcks(C)
	cccvk := s.consumerChain.App.(*appConsumer.App).ConsumerKeeper
	val := s.consAddr(a.val)
	h := int64(a.height)
	power := int64(a.power)
	kind := stakingtypes.Downtime
	if !a.isDowntime {
		kind = stakingtypes.DoubleSign
	}
	cccvk.Slash(s.ctx(C), val, h, power, sdk.Dec{}, kind) // TODO: check params here!
}

/*
~~~~~~~~~~~~
ZERO TEST
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

	s.Require().Equal(int64(19), s.height(P))
	s.Require().Equal(int64(19), s.height(C))

	s.Require().Empty(s.outbox[P])
	s.Require().Empty(s.outbox[C])

	s.Require().Equal(int64(1577923365), s.time(P).Unix())
	s.Require().Equal(int64(1577923365), s.time(C).Unix())
	s.Require().Equal(int64(1577923365), s.globalTime().Unix())

	s.Require().Equal(int64(1000000000000000000), s.delegatorBalance())

	maxValsE := uint32(2)
	maxVals := s.providerChain.App.GetStakingKeeper().GetParams(s.ctx(P)).MaxValidators

	if maxValsE != maxVals {
		s.T().Fatal("Bad test")
	}

	initialModelState := pbt.InitialModelState{
		// TODO: multiply by some 1000's
		Delegation: []int64{4, 3, 2, 1},
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
		E := initialModelState.Delegation[i] + 1
		A := s.validatorTokens(P, int64(i))
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
	ePower := []int64{5, 4}

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

func executeTrace(s *PBTTestSuite, trace Trace) {

	for _, a := range trace.Actions {
		switch a.Kind {
		case "delegate":
			s.delegate(Delegate{
				int64(a.Val),
				int64(a.Amt),
			})
		case "undelegate":
			s.undelegate(Undelegate{
				int64(a.Val),
				int64(a.Amt),
			})
		case "jumpNBlocks":
			s.jumpNBlocks(JumpNBlocks{
				a.Chains,
				int64(a.N),
				int64(a.SecondsPerBlock),
			})
		case "deliver":
			s.deliver(Deliver{a.Chain})
		case "providerSlash":
			s.providerSlash(ProviderSlash{
				int64(a.Val),
				int64(a.Power),
				int64(a.Height),
				1, // TODO: unhard code, use factor!
			})
		case "consumerSlash":
			s.consumerSlash(ConsumerSlash{
				int64(a.Val),
				int64(a.Height),
				int64(a.Power),
				a.IsDowntime,
			})
		}
	}
}

func loadTraces(fn string) []Trace {

	fd, err := os.Open(fn)

	if err != nil {
		panic(err)
	}

	defer fd.Close()

	byteValue, _ := ioutil.ReadAll(fd)

	var ret []Trace

	err = json.Unmarshal([]byte(byteValue), &ret)

	if err != nil {
		panic(err)
	}

	return ret
}

func executeTraces(s *PBTTestSuite, traces []Trace) {
	for _, trace := range traces {
		executeTrace(s, trace)
	}
}

func (s *PBTTestSuite) TestTracesHC() {
	executeTraces(s, loadTraces("trace/hc.json"))
}
