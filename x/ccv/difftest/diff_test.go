package difftest_test

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"math"
	"os"
	"testing"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/stretchr/testify/suite"

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
)

const P = "provider"
const C = "consumer"

// Equate SUT constants to model constants
func init() {
	//	Enforce tokens === power
	sdk.DefaultPowerReduction = sdk.NewInt(1)
	//	Slash factors are set to 0 because setting them !=0 will lead
	//	to numerical calculations in the staking module which are very
	//	difficult to test with differential testing (because of differences in
	//	numerical precision.
	difftest.SLASH_DOUBLESIGN = sdk.NewDec(0)
	difftest.SLASH_DOWNTIME = sdk.NewDec(0)
}

type DTTestSuite struct {
	suite.Suite

	coordinator   *ibctesting.Coordinator
	providerChain *ibctesting.TestChain
	consumerChain *ibctesting.TestChain
	path          *ibctesting.Path

	// keep around validators for easy access
	valAddresses []sdk.ValAddress

	// network for simulating relaying
	network difftest.Network

	// chain -> height of last UpdateClient for chain
	heightLastUpdateClient map[string]int64
	// chain -> array of headers for UpdateClient
	headersForUpdateClient map[string][]*ibctmtypes.Header

	// chain -> necessary to BeginBlock?
	// true if last action for chain was EndBlock
	mustBeginBlock map[string]bool

	// the current trace being executed
	trace Trace
}

type Trace struct {
	// index of trace in json
	ix int
	// index of current action
	actionIx int
	// model block data for comparisons
	blocks difftest.Blocks
	// chain -> height of last commit on chain
	// this is used to retrieve the correct block for model comparisons
	hLastCommit map[string]int64
	// have begun executing trace?
	// used to avoid model comparisons before trace has begun executing
	started bool
}

// diagnostic returns a string for diagnosing errors
func (t *Trace) diagnostic() string {
	return fmt.Sprintf("\n[diagnostic][trace %d, action %d, hLastCommit {P:%d,C:%d}]", t.ix, t.actionIx, t.hLastCommit[P], t.hLastCommit[C])

}

func TestDTTestSuite(t *testing.T) {
	suite.Run(t, new(DTTestSuite))
}

// createValidator creates an additional validator with zero commission
// and zero tokens (zero voting power).
func (s *DTTestSuite) createValidator(seedIx int) (tmtypes.PrivValidator, sdk.ValAddress) {
	privVal := difftest.GetValidatorPrivateKey(seedIx)
	pubKey, err := privVal.GetPubKey()
	s.Require().NoError(err)
	val := tmtypes.NewValidator(pubKey, 0)
	addr, err := sdk.ValAddressFromHex(val.Address.String())
	s.Require().NoError(err)
	PK := privVal.PrivKey.PubKey()
	coin := sdk.NewCoin(difftest.DENOM, sdk.NewInt(0))
	msg, err := stakingtypes.NewMsgCreateValidator(addr, PK, coin, stakingtypes.Description{}, stakingtypes.NewCommissionRates(sdk.ZeroDec(), sdk.ZeroDec(), sdk.ZeroDec()), sdk.ZeroInt())
	s.Require().NoError(err)
	pskServer := stakingkeeper.NewMsgServerImpl(s.stakingKeeperP())
	_, _ = pskServer.CreateValidator(sdk.WrapSDKContext(s.ctx(P)), msg)
	// s.Require().NoError(err)
	return privVal, addr
}

// setSigningInfos sets the validator signing info in the provider Slashing module
func (s *DTTestSuite) setSigningInfos() {
	for i := 0; i < 4; i++ {
		info := slashingtypes.NewValidatorSigningInfo(
			s.consAddr(int64(i)),
			s.height(P),
			0,
			time.Unix(0, 0),
			false,
			0,
		)
		s.providerChain.App.(*appProvider.App).SlashingKeeper.SetValidatorSigningInfo(s.ctx(P), s.consAddr(int64(i)), info)
	}
}

// bootstrapDelegate is used to delegate tokens to newly created
// validators in the setup process.
func (s *DTTestSuite) bootstrapDelegate(del int, val sdk.ValAddress, amt int) {
	d := s.providerChain.SenderAccounts[del].SenderAccount.GetAddress()
	coins := sdk.NewCoin(difftest.DENOM, sdk.NewInt(int64(amt)))
	msg := stakingtypes.NewMsgDelegate(d, val, coins)
	pskServer := stakingkeeper.NewMsgServerImpl(s.stakingKeeperP())
	_, err := pskServer.Delegate(sdk.WrapSDKContext(s.ctx(P)), msg)
	s.Require().NoError(err)
}

// Manually construct and send an empty VSC packet from the provider
// to the consumer. This is necessary to complete the handshake, and thus
// match the model init state, without any additional validator power changes.
func (s *DTTestSuite) sendEmptyVSCPacket() {
	vscID := s.providerChain.App.(*appProvider.App).ProviderKeeper.GetValidatorSetUpdateId(s.providerChain.GetContext())

	timeout := uint64(types.GetTimeoutTimestamp(s.time(P)).UnixNano())

	pd := types.NewValidatorSetChangePacketData(
		[]abci.ValidatorUpdate{},
		vscID,
		nil,
	)

	seq, ok := s.providerChain.App.(*appProvider.App).GetIBCKeeper().ChannelKeeper.GetNextSequenceSend(
		s.ctx(P), providertypes.PortID, s.path.EndpointB.ChannelID)

	s.Require().True(ok)

	packet := channeltypes.NewPacket(pd.GetBytes(), seq, providertypes.PortID, s.endpoint(P).ChannelID,
		consumertypes.PortID, s.endpoint(C).ChannelID, clienttypes.Height{}, timeout)

	channelCap := s.endpoint(P).Chain.GetChannelCapability(packet.GetSourcePort(), packet.GetSourceChannel())

	err := s.endpoint(P).Chain.App.GetIBCKeeper().ChannelKeeper.SendPacket(s.ctx(P), channelCap, packet)

	s.Require().NoError(err)

	s.jumpNBlocks([]string{P}, 2, 1)

	s.idempotentUpdateClient(C)

	ack, err := difftest.TryRecvPacket(s.endpoint(P), s.endpoint(C), packet)
	s.network.AddAck(C, ack, packet)

	s.Require().NoError(err)
}

// Checks that the lexicographic ordering of validator addresses as computed in
// the staking module match the ordering of validators in the model.
func (s *DTTestSuite) ensureValidatorLexicographicOrderingMatchesModel(lesser sdk.ValAddress, greater sdk.ValAddress) {
	lesserV, _ := s.stakingKeeperP().GetValidator(s.ctx(P), lesser)
	greaterV, _ := s.stakingKeeperP().GetValidator(s.ctx(P), greater)
	lesserKey := stakingtypes.GetValidatorsByPowerIndexKey(lesserV, sdk.DefaultPowerReduction)
	greaterKey := stakingtypes.GetValidatorsByPowerIndexKey(greaterV, sdk.DefaultPowerReduction)
	// The result will be 0 if a==b, -1 if a < b, and +1 if a > b.
	res := bytes.Compare(lesserKey, greaterKey)
	// Confirm that validator precedence is the same in code as in model
	s.Require().Equal(-1, res)
}

// SetupTest sets up the test suite in a 'zero' state which is ready
// to have a trace executed against it.
// A zero state is a state in which two chains, a Provider and Consumer
// are in communication via IBC and CCV and for which the validator
// sets on both chains are equal.
// Thus, in the zero state, the governance proposal and handshake
// components of the Interchain Security lifecycle are complete.
// The zero state is exactly the state that the model is initialized to.
func (s *DTTestSuite) SetupTest() {

	// init utility data structures
	s.network = difftest.MakeNetwork()
	s.heightLastUpdateClient = map[string]int64{P: 0, C: 0}
	s.headersForUpdateClient = map[string][]*ibctmtypes.Header{P: {}, C: {}}
	s.mustBeginBlock = map[string]bool{P: true, C: true}
	s.trace = Trace{}

	// Create the provider and consumer chains.
	// The provider chain is bootstrapped with 1 delegator account.
	// The chains are bootstrapped with 2 (active) validators.
	s.coordinator, s.providerChain, s.consumerChain, s.valAddresses = difftest.NewDTProviderConsumerCoordinator(s.T())

	// Diff testing tests scenarios in which the validator set changes.
	// 4 validators in total are used. To allow for both jailed validators,
	// and for validators to fall out of the active set regardless of jail status,
	// (max) 2 active validators are used.
	// The chains are initially created with the 2 (active) validators,
	// thus, here we create the 2 additional validators.
	for i := 2; i < 4; i++ {
		val, addr := s.createValidator(i)
		pubKey, err := val.GetPubKey()
		s.Require().Nil(err)
		s.valAddresses = append(s.valAddresses, addr)
		s.providerChain.Signers[pubKey.Address().String()] = val
		s.consumerChain.Signers[pubKey.Address().String()] = val
	}

	// Set the signing info in the slashing module for all validators to allow
	// correct jailing behaviors.
	s.setSigningInfos()

	// In order to match the model to the system under test it is necessary
	// to enforce a strict lexicographic ordering on the validators.
	// We must do this because the staking module will break ties when
	// deciding the active validator set by comparing addresses lexicographically.
	// Thus, we assert here that the ordering in the model matches the ordering
	// in the SUT.
	for i := range s.valAddresses[:len(s.valAddresses)-1] {
		// validators are chosen sorted descending in the staking module
		greater := s.valAddresses[i]
		lesser := s.valAddresses[i+1]
		s.ensureValidatorLexicographicOrderingMatchesModel(lesser, greater)
	}

	// Commit the additional validators
	s.coordinator.CommitBlock(s.providerChain)

	// Configure tendermint parameters to match the model and allow
	// compressed timescales.
	tmConfig := ibctesting.NewTendermintConfig()
	tmConfig.UnbondingPeriod = difftest.UNBONDING_P
	tmConfig.TrustingPeriod = difftest.TRUSTING
	tmConfig.MaxClockDrift = difftest.MAX_CLOCK_DRIFT

	// Create Provider client
	providerClient := ibctmtypes.NewClientState(
		s.providerChain.ChainID, tmConfig.TrustLevel, tmConfig.TrustingPeriod, tmConfig.UnbondingPeriod, tmConfig.MaxClockDrift,
		s.providerChain.LastHeader.GetHeight().(clienttypes.Height), commitmenttypes.GetSDKSpecs(), []string{"upgrade", "upgradedIBCState"}, tmConfig.AllowUpdateAfterExpiry, tmConfig.AllowUpdateAfterMisbehaviour,
	)
	providerConsState := s.providerChain.LastHeader.ConsensusState()

	// Create Consumer genesis
	valUpdates := tmtypes.TM2PB.ValidatorUpdates(s.providerChain.Vals)
	params := consumertypes.NewParams(
		true,
		1000, // ignore distribution
		"",   // ignore distribution
		"",   // ignore distribution
	)
	consumerGenesis := consumertypes.NewInitialGenesisState(providerClient, providerConsState, valUpdates, params)
	ck := s.consumerChain.App.(*appConsumer.App).ConsumerKeeper
	ck.InitGenesis(s.ctx(C), consumerGenesis)

	// Configure the ibc path
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
	s.path.EndpointA.ClientID = providerClientId
	err := s.path.EndpointB.Chain.SenderAccount.SetAccountNumber(6)
	s.Require().NoError(err)
	err = s.path.EndpointA.Chain.SenderAccount.SetAccountNumber(1)
	s.Require().NoError(err)

	// Configure and create the consumer Client
	tmConfig = s.path.EndpointB.ClientConfig.(*ibctesting.TendermintConfig)
	tmConfig.UnbondingPeriod = difftest.UNBONDING_P
	tmConfig.TrustingPeriod = difftest.TRUSTING
	tmConfig.MaxClockDrift = difftest.MAX_CLOCK_DRIFT
	err = s.path.EndpointB.CreateClient()
	s.Require().NoError(err)

	// Create the Consumer chain ID mapping in the provider state
	s.providerChain.App.(*appProvider.App).ProviderKeeper.SetConsumerClientId(s.ctx(P), s.consumerChain.ChainID, s.path.EndpointB.ClientID)

	// Handshake
	s.coordinator.CreateConnections(s.path)
	s.coordinator.CreateChannels(s.path)

	// Set the unbonding time on the consumer to the model value
	ck.SetUnbondingTime(s.ctx(C), difftest.UNBONDING_C)

	// Send an empty VSC packet from the provider to the consumer to finish
	// the handshake. This is necessary because the model starts from a
	// completely initialized state, with a completed handshake.
	s.sendEmptyVSCPacket()

	s.jumpNBlocks([]string{P}, 1, 1)
	s.jumpNBlocks([]string{C}, 4, 1)

	// Begin new blocks to allow delegation
	s.idempotentBeginBlock(P)
	s.idempotentBeginBlock(C)

	// Delegate some tokens to the 2 newly created additional validators.
	// The delegations from addr 0 are 'true' delegations, while the delegations
	// from addr 1 are used to mimic MinSelfDelegation, and to prevent validator
	// deletion in the case that 'true' delegations fall to 0 in the course of the trace.
	s.bootstrapDelegate(0, s.validator(2), 2*difftest.TOKEN_SCALAR) // 2 ensures strict val order
	s.bootstrapDelegate(0, s.validator(3), 1*difftest.TOKEN_SCALAR)
	s.bootstrapDelegate(1, s.validator(2), 1*difftest.TOKEN_SCALAR)
	s.bootstrapDelegate(1, s.validator(3), 1*difftest.TOKEN_SCALAR)

	// Set the slash factors on the provider to match the model
	sparams := s.providerChain.App.(*appProvider.App).SlashingKeeper.GetParams(s.ctx(P))
	sparams.SlashFractionDoubleSign = difftest.SLASH_DOUBLESIGN
	sparams.SlashFractionDowntime = difftest.SLASH_DOWNTIME
	s.providerChain.App.(*appProvider.App).SlashingKeeper.SetParams(s.ctx(P), sparams)

	s.jumpNBlocks([]string{P, C}, 40, 5)
	// Deliver the empty VSC packet in order to complete handshake
	s.deliver(P, 1)
	s.jumpNBlocks([]string{P, C}, 40, 5)

	// Begin new blocks. This matches the SUT state to the model state
	// and prepares the chains for actions.
	s.idempotentBeginBlock(P)
	s.idempotentBeginBlock(C)
}

// ctx returns the sdk.Context for the chain
func (s *DTTestSuite) ctx(chain string) sdk.Context {
	return s.chain(chain).GetContext()
}

// chain returns the TestChain for a given chain identifier
func (s *DTTestSuite) chain(chain string) *ibctesting.TestChain {
	return map[string]*ibctesting.TestChain{P: s.providerChain, C: s.consumerChain}[chain]
}

// other returns the counterparty chain
func (s *DTTestSuite) other(chain string) string {
	return map[string]string{P: C, C: P}[chain]
}

// height returns the height of the current header of chain
func (s *DTTestSuite) height(chain string) int64 {
	return s.chain(chain).CurrentHeader.GetHeight()
}

// time returns the time of the current header of chain
func (s *DTTestSuite) time(chain string) time.Time {
	return s.chain(chain).CurrentHeader.Time
}

// globalTime returns the current global time of the test suite
func (s *DTTestSuite) globalTime() time.Time {
	return s.coordinator.CurrentTime
}

// endpoint returns the ibc Endpoint for the chain
func (s *DTTestSuite) endpoint(chain string) *ibctesting.Endpoint {
	return map[string]*ibctesting.Endpoint{P: s.path.EndpointB, C: s.path.EndpointA}[chain]
}

// delegator retrieves the address for the (sole) delegator account
func (s *DTTestSuite) delegator() sdk.AccAddress {
	return s.providerChain.SenderAccount.GetAddress()
}

// validator returns the address for the validator with id (ix) i
func (s *DTTestSuite) validator(i int64) sdk.ValAddress {
	return s.valAddresses[i]
}

// consAddr returns the ConsAdd for the validator with id (ix) i
func (s *DTTestSuite) consAddr(i int64) sdk.ConsAddress {
	return sdk.ConsAddress(s.validator(i))
}

// stakingKeeperP returns the staking keeper for the provider chain
func (s *DTTestSuite) stakingKeeperP() stakingkeeper.Keeper {
	return s.providerChain.App.(*appProvider.App).StakingKeeper
}

// isJailed returns the jail status of validator with id (ix) i
func (s *DTTestSuite) isJailed(i int64) bool {
	val, found := s.stakingKeeperP().GetValidator(s.ctx(P), s.validator(i))
	if !found {
		s.T().Fatal("GetValidator() -> !found")
	}
	return val.IsJailed()
}

// consumerPower returns the power on the consumer chain for
// validator with id (ix) i
func (s *DTTestSuite) consumerPower(i int64) (int64, error) {
	ck := s.consumerChain.App.(*appConsumer.App).ConsumerKeeper

	v, found := ck.GetCCValidator(s.ctx(C), s.validator(i))
	if !found {
		return 0, fmt.Errorf("GetCCValidator() -> !found")
	}
	return v.Power, nil
}

// delegation returns the number of delegated tokens in the delegation from
// the (sole) delegator account to the validator with id (ix) i
func (s *DTTestSuite) delegation(i int64) int64 {
	d, found := s.stakingKeeperP().GetDelegation(s.ctx(P), s.delegator(), s.validator(i))
	if !found {
		s.T().Fatal("GetDelegation() -> !found")
	}
	return d.Shares.TruncateInt64()
}

// validatorStatus returns the validator status for validator with id (ix) i
// on the provider chain
func (s *DTTestSuite) validatorStatus(i int64) stakingtypes.BondStatus {
	v, found := s.stakingKeeperP().GetValidator(s.ctx(P), s.validator(i))
	if !found {
		s.T().Fatal("GetValidator() -> !found")
	}
	return v.GetStatus()
}

// providerTokens returns the number of tokens that the validator with
// id (ix) i has delegated to it in total on the provider chain
func (s *DTTestSuite) providerTokens(i int64) int64 {
	v, found := s.stakingKeeperP().GetValidator(s.ctx(P), s.validator(i))
	if !found {
		s.T().Fatal("GetValidator() -> !found")
	}
	return v.Tokens.Int64()
}

// delegatorBalance returns the balance of the (sole) delegator account
func (s *DTTestSuite) delegatorBalance() int64 {
	d := s.delegator()
	app := s.providerChain.App.(*appProvider.App)
	bal := app.BankKeeper.GetBalance(s.ctx(P), d, difftest.DENOM)
	return bal.Amount.Int64()
}

// idempotentBeginBlock begins a new block on chain
// if it necessary to do so. It is necessary if
// mustBeginBlock[chain] is true, which is the case
// when the last action for the chain was EndBlock
func (s *DTTestSuite) idempotentBeginBlock(chain string) {
	if s.mustBeginBlock[chain] {

		s.mustBeginBlock[chain] = false

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

		s.idempotentUpdateClient(chain)
	}
}

// idempotentDeliverAcks will deliver any acks available on the network
// which have been emitted by the counterparty chain since the last
// call to idempotentDeliverAcks
func (s *DTTestSuite) idempotentDeliverAcks(receiver string) {
	for _, ack := range s.network.ConsumeAcks(s.other(receiver)) {
		s.idempotentUpdateClient(receiver)
		err := difftest.TryRecvAck(s.endpoint(s.other(receiver)), s.endpoint(receiver), ack.Packet, ack.Ack)
		s.Require().NoError(err)
	}
}

// idempotentUpdateClient will bring the client on chain
// up to date by delivering each header committed on the
// counterparty chain since the last idempotentUpdateClient
func (s DTTestSuite) idempotentUpdateClient(chain string) {
	otherHeight := s.height(s.other(chain))
	if s.heightLastUpdateClient[chain] < otherHeight {
		for _, header := range s.headersForUpdateClient[s.other(chain)] {
			err := difftest.UpdateReceiverClient(s.endpoint(s.other(chain)), s.endpoint(chain), header)
			if err != nil {
				s.FailNow("Bad test")
			}
		}
		s.headersForUpdateClient[s.other(chain)] = []*ibctmtypes.Header{}
		s.heightLastUpdateClient[chain] = otherHeight
	}

}

// delegate delegates amt tokens to validator val
func (s *DTTestSuite) delegate(val int64, amt int64) {
	// Make sure block has begun
	s.idempotentBeginBlock(P)
	// Deliver any outstanding acks
	s.idempotentDeliverAcks(P)
	server := stakingkeeper.NewMsgServerImpl(s.stakingKeeperP())
	coin := sdk.NewCoin(difftest.DENOM, sdk.NewInt(amt))
	d := s.delegator()
	v := s.validator(val)
	msg := stakingtypes.NewMsgDelegate(d, v, coin)
	_, err := server.Delegate(sdk.WrapSDKContext(s.ctx(P)), msg)
	s.Require().NoError(err)
}

// undelegate undelegates amt tokens from validator val
func (s *DTTestSuite) undelegate(val int64, amt int64) {
	// Make sure block has begun
	s.idempotentBeginBlock(P)
	// Deliver any outstanding acks
	s.idempotentDeliverAcks(P)
	server := stakingkeeper.NewMsgServerImpl(s.stakingKeeperP())
	coin := sdk.NewCoin(difftest.DENOM, sdk.NewInt(amt))
	d := s.delegator()
	v := s.validator(val)
	msg := stakingtypes.NewMsgUndelegate(d, v, coin)
	_, err := server.Undelegate(sdk.WrapSDKContext(s.ctx(P)), msg)
	s.Require().NoError(err)
}

// enableCtx allows querying the chain even before beginBlock call
// This function is necessary to allow accessing the Context for the
// chain after EndBlock but before the next model based BeginBlock
// A new header is created and BeginBlock is called, which creates
// a ctx object. However this header will be overwritten when
// beginBlock is called by jumpNBlocks.
func (s *DTTestSuite) enableCtx(chain string) {
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

// endBlock calls the endblocker of the chain, commits the block to tendermint
// and applies validator set changes. It also collects packets and adds them
// to the network.
func (s *DTTestSuite) endBlock(chain string) {

	// Make sure block has started
	s.idempotentBeginBlock(chain)
	// Deliver any outstanding acks
	s.idempotentDeliverAcks(chain)

	c := s.chain(chain)

	ebRes := c.App.EndBlock(abci.RequestEndBlock{Height: c.CurrentHeader.Height})

	if s.trace.started {
		// If the trace has started we match the state of the SUT to the model state.
		// If the trace has not started (if this method is called during setup) then
		// we omit the comparison.
		// It is important that this occurs before App.Commit as the Context is needed
		// for queries.
		s.trace.hLastCommit[chain] += 1
		s.matchState(chain)
	}

	c.App.Commit()

	c.Vals = c.NextVals

	c.NextVals = ibctesting.ApplyValSetChanges(c.T, c.Vals, ebRes.ValidatorUpdates)

	c.LastHeader = c.CurrentTMClientHeader()
	// Store header to be used in UpdateClient
	s.headersForUpdateClient[chain] = append(s.headersForUpdateClient[chain], c.LastHeader)

	for _, e := range ebRes.Events {
		if e.Type == channeltypes.EventTypeSendPacket {
			packet, err := channelkeeper.ReconstructPacketFromEvent(e)
			s.Require().NoError(err)
			// Collect packets
			s.network.AddPacket(chain, packet)
		}
	}

	// Commit packets emmitted up to this point
	s.network.Commit(chain)

	// Register to begin a new block
	s.mustBeginBlock[chain] = true

	// Enable using Context object for queries
	s.enableCtx(chain)
}

// jumpNBlocks progresses the blockchain on one or both chains.
// In this manner, it is possible for chains to advance in (almost) lock-step or
// separately (somewhat asynchronously).
func (s *DTTestSuite) jumpNBlocks(chains []string, n int64, secondsPerBlock int64) {
	for i := int64(0); i < n; i++ {
		for _, c := range chains { // [P] or [P, C] or [C]
			s.endBlock(c)
		}
		// When a chain starts a new block, it takes the global time. By advancing the global time after
		// a chain commits a block, it is possible to test long gaps between blocks.
		s.coordinator.CurrentTime = s.coordinator.CurrentTime.Add(time.Second * time.Duration(secondsPerBlock)).UTC()
	}
}

// deliver numPackets packets from the network to chain
func (s *DTTestSuite) deliver(chain string, numPackets int64) {
	// Make sure block has started
	s.idempotentBeginBlock(chain)
	// Deliver any outstanding acks
	s.idempotentDeliverAcks(chain)
	// Make sure client is updated
	s.idempotentUpdateClient(chain)
	// Consume deliverable packets from the network
	packets := s.network.ConsumePackets(s.other(chain), numPackets)
	for _, p := range packets {
		receiver := s.endpoint(chain)
		sender := receiver.Counterparty
		ack, err := difftest.TryRecvPacket(sender, receiver, p.Packet)
		if err != nil {
			s.FailNow(s.trace.diagnostic()+"relay failed", err)
		}
		s.network.AddAck(chain, ack, p.Packet)
	}
}

// consumerSlash simulates a slash event occurring on the consumer chain
// it can be for a downtime or doublesign
func (s *DTTestSuite) consumerSlash(val sdk.ConsAddress, h int64, isDowntime bool) {
	// Make sure block has started
	s.idempotentBeginBlock(C)
	// Deliver any outstanding acks
	s.idempotentDeliverAcks(C)
	kind := stakingtypes.DoubleSign
	if isDowntime {
		kind = stakingtypes.Downtime
	}
	ctx := s.ctx(C)
	before := len(ctx.EventManager().Events())
	ck := s.consumerChain.App.(*appConsumer.App).ConsumerKeeper
	ck.Slash(ctx, val, h, 0, sdk.Dec{}, kind)
	evts := ctx.EventManager().ABCIEvents()
	for _, e := range evts[before:] {
		if e.Type == channeltypes.EventTypeSendPacket {
			packet, err := channelkeeper.ReconstructPacketFromEvent(e)
			s.Require().NoError(err)
			// Collect any packets which may be emitted as a result of the action
			s.network.AddPacket(C, packet)
		}
	}
}

// matchState checks that the state in the model matches the current
// state in the SUT for the given chain
func (s *DTTestSuite) matchState(chain string) {
	// Model time starts at 0 so we need an offset for comparisons.
	// Subtract 5 seconds because matchState is done after ending a block but
	// before the new block begins, while the model state uses an already
	// begun next block.
	modelTimeOffset := time.Unix(difftest.SUT_TIME_OFFSET, 0).UTC().Add(time.Second * time.Duration(-5))

	trace := s.trace
	// Get a diagnostic for debugging
	diagnostic := trace.diagnostic()

	if chain == P {
		ss := trace.blocks.Provider[trace.hLastCommit[P]].Snapshot
		// Check height
		s.Require().Equalf(int64(ss.H.Provider+int(difftest.MODEL_HEIGHT_OFFSET)), s.height(P), diagnostic+"P height mismatch")
		// Check time
		modelTime := time.Second * time.Duration(ss.T.Provider)
		s.Require().Equalf(modelTimeOffset.Add(modelTime), s.time(P), diagnostic+"P time mismatch")
		// Check delegator balance
		s.Require().Equalf(int64(ss.DelegatorTokens), s.delegatorBalance(), diagnostic+"P del balance mismatch")
		// Check jailing status for each validator
		for j, jailedUntilTimestamp := range ss.Jailed {
			s.Require().Equalf(jailedUntilTimestamp != nil, s.isJailed(int64(j)), diagnostic+"P jail status mismatch for val %d", j)
		}
		// Check tokens
		for j, tokens := range ss.Tokens {
			s.Require().Equalf(int64(tokens), s.providerTokens(int64(j)), diagnostic+"P tokens mismatch for val %d", j)
		}
	}
	if chain == C {
		ss := trace.blocks.Consumer[trace.hLastCommit[C]].Snapshot
		// Check height
		s.Require().Equalf(int64(ss.H.Consumer+int(difftest.MODEL_HEIGHT_OFFSET)), s.height(C), diagnostic+"C height mismatch")
		// Check time
		modelTime := time.Second * time.Duration(ss.T.Consumer)
		s.Require().Equalf(modelTimeOffset.Add(modelTime), s.time(C), diagnostic+"C time mismatch")
		// Check the validator powers
		for j, power := range ss.Power {
			actual, err := s.consumerPower(int64(j))
			if power != nil {
				s.Require().Nilf(err, diagnostic+"C validator not found")
				s.Require().Equalf(int64(*power), actual, diagnostic+"C power mismatch for val %d", j)
			} else {
				s.Require().Errorf(err, diagnostic+"C power mismatch for val %d, expect 0 (nil), got %d", j, actual)
			}
		}
	}
}

// executeTrace w
func executeTrace(s *DTTestSuite, trace difftest.TraceData) {
	for i, action := range trace.Actions {
		a := action.Action
		// Record the action index for diagnostics
		s.trace.actionIx = i
		switch a.Kind {
		case "Delegate":
			s.delegate(
				int64(a.Val),
				int64(a.Amt),
			)
		case "Undelegate":
			s.undelegate(
				int64(a.Val),
				int64(a.Amt),
			)
		case "JumpNBlocks":
			s.jumpNBlocks(
				a.Chains,
				int64(a.N),
				int64(a.SecondsPerBlock),
			)
		case "Deliver":
			s.deliver(a.Chain, int64(a.NumPackets))
		case "ConsumerSlash":
			s.consumerSlash(
				s.consAddr(int64(a.Val)),
				// The SUT height is greater than the model height
				// because the SUT has to do initialization.
				int64(a.InfractionHeight)+difftest.MODEL_HEIGHT_OFFSET,
				a.IsDowntime,
			)
		default:
			s.Require().FailNow("Failed to parse action")
		}
	}
}

// Test a set of traces
func (s *DTTestSuite) TestTraces() {
	traces := loadTraces("traces.json")
	for i, trace := range traces {
		s.Run(fmt.Sprintf("Trace num: %d", i), func() {
			// Setup a new pair of chains for each trace
			s.SetupTest()
			defer func() {
				// If a panic occurs, we trap it to print a diagnostic
				// and improve debugging experience.
				if r := recover(); r != nil {
					fmt.Println(s.trace.diagnostic())
					fmt.Println(r)
					panic("Panic occurred during difftest TestTraces")
				}
			}()
			// Record information about the trace, for debugging
			// diagnostics.
			s.trace = Trace{
				i,
				0,
				trace.Blocks,
				map[string]int64{P: 0, C: 0},
				true,
			}
			executeTrace(s, trace)
		})
	}
}

func loadTraces(fn string) []difftest.TraceData {

	fd, err := os.Open(fn)

	if err != nil {
		panic(err)
	}

	defer fd.Close()

	byteValue, _ := io.ReadAll(fd)

	var ret []difftest.TraceData

	err = json.Unmarshal([]byte(byteValue), &ret)

	if err != nil {
		panic(err)
	}

	return ret
}

// TestAssumptions tests that the assumptions used to write the difftest
// driver hold. This test therefore does not test the system, but only that
// the driver is correctly setup.
func (s *DTTestSuite) TestAssumptions() {

	const FAIL_MESSAGE = "Diff test assumptions failed. There is a problem with the test driver."

	// Check that each validator has signing info
	for i := 0; i < 4; i++ {
		_, found := s.providerChain.App.(*appProvider.App).SlashingKeeper.GetValidatorSigningInfo(s.ctx(P), s.consAddr(int64(i)))
		if !found {
			s.Require().FailNow(FAIL_MESSAGE)
		}
	}

	// Check that downtime and doublesign slash factors are correctly set.
	s.Require().Equal(difftest.SLASH_DOWNTIME, s.providerChain.App.(*appProvider.App).SlashingKeeper.SlashFractionDowntime(s.ctx(P)))
	s.Require().Equal(difftest.SLASH_DOUBLESIGN, s.providerChain.App.(*appProvider.App).SlashingKeeper.SlashFractionDoubleSign(s.ctx(P)))

	// Check that unbondingTime is correctly set in staking module
	stakeParams := s.stakingKeeperP().GetParams(s.ctx(P))
	s.Require().Equal(stakeParams.UnbondingTime, difftest.UNBONDING_P)
	// Check that unbondingTime is correctly set on consumer
	s.Require().Equal(
		s.consumerChain.App.(*appConsumer.App).ConsumerKeeper.UnbondingTime(s.ctx(C)),
		difftest.UNBONDING_C)

	// Check that both chains are ready to begin a new block
	s.Require().Equal(false, s.mustBeginBlock[P])
	s.Require().Equal(false, s.mustBeginBlock[C])

	// Check that the heights of both chains match the model
	// (A +1 is needed because the model always invisibly increases the height by 1
	// as a first step)
	s.Require().Equal(0+1+difftest.MODEL_HEIGHT_OFFSET, s.height(P))
	s.Require().Equal(0+1+difftest.MODEL_HEIGHT_OFFSET, s.height(C))

	// Check that no packets are in the network
	s.Require().Empty(s.network.OutboxPackets[P])
	s.Require().Empty(s.network.OutboxPackets[C])

	// Check that both chains and the global time are zero'd (equal offset)
	s.Require().Equal(int64(difftest.SUT_TIME_OFFSET), s.time(P).Unix())
	s.Require().Equal(int64(difftest.SUT_TIME_OFFSET), s.time(C).Unix())
	s.Require().Equal(int64(difftest.SUT_TIME_OFFSET), s.globalTime().Unix())

	// Check that the delegator account has the correct initial balance
	s.Require().Equal(int64(difftest.DELEGATOR_INITIAL_BALANCE), s.delegatorBalance())

	// Check that the maxValidators param is sset correctly in the staking module
	maxValsE := uint32(2)
	maxVals := s.stakingKeeperP().GetParams(s.ctx(P)).MaxValidators

	if maxValsE != maxVals {
		s.T().Fatal(FAIL_MESSAGE)
	}

	// Check that the initial delegations to each validator are correctly
	// initialised to match the model.
	// Also check that the bond status for each validator match the model.
	initialModelState := difftest.InitialModelValidatorState{
		Delegation: []int64{4 * difftest.TOKEN_SCALAR, 3 * difftest.TOKEN_SCALAR, 2 * difftest.TOKEN_SCALAR, 1 * difftest.TOKEN_SCALAR},
		Status:     []stakingtypes.BondStatus{stakingtypes.Bonded, stakingtypes.Bonded, stakingtypes.Unbonded, stakingtypes.Unbonded},
	}
	for i := 0; i < 4; i++ {
		E := initialModelState.Delegation[i]
		A := s.delegation(int64(i))
		if E != A {
			s.T().Fatal(FAIL_MESSAGE)
		}
	}
	for i := 0; i < 4; i++ {
		E := initialModelState.Delegation[i] + difftest.TOKEN_SCALAR
		A := s.providerTokens(int64(i))
		if E != A {
			s.T().Fatal(FAIL_MESSAGE)
		}
	}
	for i := 0; i < 4; i++ {
		E := initialModelState.Status[i]
		A := s.validatorStatus(int64(i))
		if E != A {
			s.T().Fatal(FAIL_MESSAGE)
		}
	}

	sk := s.stakingKeeperP()

	// Check that there are no unbonding delegations in the staking module
	sk.IterateUnbondingDelegations(s.ctx(P),
		func(index int64, ubd stakingtypes.UnbondingDelegation) bool {
			s.T().Fatal(FAIL_MESSAGE)
			return false // Don't stop
		})

	// Check that there are no redelegations in the staking module
	sk.IterateRedelegations(s.ctx(P),
		func(index int64, ubd stakingtypes.Redelegation) bool {
			s.T().Fatal(FAIL_MESSAGE)
			return false // Don't stop
		})

	// Check that there are no unbonding validators in the staking module
	endTime := time.Unix(math.MaxInt64, 0)
	endHeight := int64(math.MaxInt64)
	unbondingValIterator := sk.ValidatorQueueIterator(s.ctx(P), endTime, endHeight)
	defer unbondingValIterator.Close()
	for ; unbondingValIterator.Valid(); unbondingValIterator.Next() {
		s.T().Fatal(FAIL_MESSAGE)
	}

	// Check that the validator powers on the consumer chain are correct
	eFound := []bool{true, true, false, false}
	ePower := []int64{5 * difftest.TOKEN_SCALAR, 4 * difftest.TOKEN_SCALAR}

	ck := s.consumerChain.App.(*appConsumer.App).ConsumerKeeper

	for i := 0; i < 4; i++ {
		addr := s.validator(int64(i))
		val, found := ck.GetCCValidator(s.ctx(C), addr)
		s.Require().Equal(eFound[i], found)
		if eFound[i] {
			if ePower[i] != val.Power {
				s.T().Fatal(FAIL_MESSAGE)
			}
		}
	}

	s.Require().Empty(ck.GetPendingSlashRequests(s.ctx(C)))

	// Check that the number of maturing VSC ids on the consumer is exactly 1
	// It should be exactly 1 because a VSC is sent to the consumer to finish
	// the handshake/initialization.
	var numUnbondingTimes = 0
	ck.IteratePacketMaturityTime(s.ctx(C),
		func(vscId uint64, timeNs uint64) bool {
			numUnbondingTimes += 1
			if 1 < numUnbondingTimes {
				s.T().Fatal(FAIL_MESSAGE)
			}
			return false // Don't stop
		})
}

// go test -coverprofile=coverage.out ./...
// go test -coverprofile=coverage.out -coverpkg=./... -timeout 1000m -run TestDTTestSuite/TestTraces x/ccv/difftest/diff_test.go | tee debug.txt
