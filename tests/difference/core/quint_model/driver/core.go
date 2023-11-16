package main

import (
	"fmt"
	"strings"
	"testing"
	"time"

	ibctesting "github.com/cosmos/ibc-go/v7/testing"
	"github.com/stretchr/testify/require"

	sdk "github.com/cosmos/cosmos-sdk/types"
	slashingkeeper "github.com/cosmos/cosmos-sdk/x/slashing/keeper"
	stakingkeeper "github.com/cosmos/cosmos-sdk/x/staking/keeper"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	consumertypes "github.com/cosmos/interchain-security/v3/x/ccv/consumer/types"

	appConsumer "github.com/cosmos/interchain-security/v3/app/consumer"
	appProvider "github.com/cosmos/interchain-security/v3/app/provider"

	simibc "github.com/cosmos/interchain-security/v3/testutil/simibc"
	consumerkeeper "github.com/cosmos/interchain-security/v3/x/ccv/consumer/keeper"
	providerkeeper "github.com/cosmos/interchain-security/v3/x/ccv/provider/keeper"

	cmttypes "github.com/cometbft/cometbft/types"
)

// Define a new type for ChainIds to be more explicit
// about what the string represents.
type ChainId string

type ModelParams struct {
	VscTimeout              time.Duration
	CcvTimeout              map[ChainId]time.Duration
	UnbondingPeriodPerChain map[ChainId]time.Duration
	TrustingPeriodPerChain  map[ChainId]time.Duration
}

type Driver struct {
	t *testing.T

	coordinator *ibctesting.Coordinator

	// simulate IBC network: for each consumer chain name, we have a path between consumer and provider
	simibcs map[ChainId]*simibc.RelayedPath

	// keep around validators for easy access
	validators []*cmttypes.Validator
	valNames   []string
}

// ctx returns the sdk.Context for the chain
func (s *Driver) ctx(chain ChainId) sdk.Context {
	return s.chain(chain).GetContext()
}

// returns the path from the given chain to the provider.
func (s *Driver) path(chain ChainId) *simibc.RelayedPath {
	return s.simibcs[chain]
}

// chain returns the TestChain for a given chain identifier
func (s *Driver) chain(chain ChainId) *ibctesting.TestChain {
	return s.coordinator.GetChain(string(chain))
}

func (s *Driver) providerChain() *ibctesting.TestChain {
	return s.chain("provider")
}

func (s *Driver) providerCtx() sdk.Context {
	return s.providerChain().GetContext()
}

func (s *Driver) providerKeeper() providerkeeper.Keeper {
	return s.providerChain().App.(*appProvider.App).ProviderKeeper
}

func (b *Driver) providerStakingKeeper() stakingkeeper.Keeper {
	return *b.providerChain().App.(*appProvider.App).StakingKeeper
}

func (b *Driver) providerSlashingKeeper() slashingkeeper.Keeper {
	return b.providerChain().App.(*appProvider.App).SlashingKeeper
}

func (b *Driver) consumerKeeper(chain ChainId) consumerkeeper.Keeper {
	return b.chain(chain).App.(*appConsumer.App).ConsumerKeeper
}

// height returns the height of the current header of chain
func (s *Driver) height(chain ChainId) int64 {
	return s.chain(chain).CurrentHeader.GetHeight()
}

// time returns the time of the current header of chain
func (s *Driver) time(chain ChainId) time.Time {
	return s.chain(chain).CurrentHeader.Time
}

// delegator retrieves the address for the delegator account
func (s *Driver) delegator() sdk.AccAddress {
	return s.providerChain().SenderAccount.GetAddress()
}

// validator returns the address for the validator with id (ix) i
func (s *Driver) validator(i int64) sdk.ValAddress {
	return sdk.ValAddress(s.validators[i].Address)
}

// consAddr returns the ConsAdd for the validator with id (ix) i
func (s *Driver) consAddr(i int64) sdk.ConsAddress {
	return sdk.ConsAddress(s.validator(i))
}

// isJailed returns the jail status of validator with id (ix) i
func (s *Driver) isJailed(i int64) bool {
	val, found := s.providerStakingKeeper().GetValidator(s.ctx(P), s.validator(i))

	require.True(s.t, found, "GetValidator(%v) -> !found", s.validator(i))
	return val.IsJailed()
}

// consumerPower returns the power on the consumer chain chain for
// validator with id (ix) i
func (s *Driver) consumerPower(i int64, chain ChainId) (int64, error) {
	v, found := s.consumerKeeper(chain).GetCCValidator(s.ctx(chain), s.validator(i))
	if !found {
		return 0, fmt.Errorf("GetCCValidator(%v) -> !found", s.validator(i))
	}
	return v.Power, nil
}

// consumerTokens returns the number of tokens that the validator with
// id (ix) i has delegated to it in total on the provider chain
func (s *Driver) providerPower(i int64) int64 {
	v, found := s.providerStakingKeeper().GetValidator(s.ctx(P), s.validator(i))
	require.True(s.t, found, "GetValidator(%v) -> !found", s.validator(i))
	return v.BondedTokens().Int64()
}

// delegation returns the number of delegated tokens in the delegation from
// the delegator account to the validator with id (ix) i
func (s *Driver) delegation(i int64) int64 {
	d, found := s.providerStakingKeeper().GetDelegation(s.ctx(P), s.delegator(), s.validator(i))
	require.True(s.t, found, "GetDelegation(%v) -> !found", s.validator(i))
	return d.Shares.TruncateInt64()
}

// validatorStatus returns the validator status for validator with id (ix) i
// on the provider chain
func (s *Driver) validatorStatus(i int64) stakingtypes.BondStatus {
	v, found := s.providerStakingKeeper().GetValidator(s.ctx(P), s.validator(i))
	require.True(s.t, found, "GetValidator(%v) -> !found", s.validator(i))
	return v.GetStatus()
}

// providerTokens returns the number of tokens that the validator with
// id (ix) i has delegated to it in total on the provider chain
func (s *Driver) providerTokens(i int64) int64 {
	v, found := s.providerStakingKeeper().GetValidator(s.ctx(P), s.validator(i))
	if !found {
		return 0
	}
	return v.Tokens.Int64()
}

func (s *Driver) providerValidatorSet(chain ChainId) []stakingtypes.Validator {
	return s.providerStakingKeeper().GetAllValidators(s.ctx(P))
}

func (s *Driver) consumerValidatorSet(chain ChainId) []consumertypes.CrossChainValidator {
	return s.consumerKeeper(chain).GetAllCCValidator(s.ctx(chain))
}

// delegatorBalance returns the balance of the delegator account
func (s *Driver) delegatorBalance() int64 {
	d := s.delegator()
	bal := s.providerChain().App.(*appProvider.App).BankKeeper.GetBalance(s.ctx(P), d, sdk.DefaultBondDenom)
	return bal.Amount.Int64()
}

// delegate delegates amt tokens to validator val
func (s *Driver) delegate(val, amt int64) {
	providerStaking := s.providerStakingKeeper()
	server := stakingkeeper.NewMsgServerImpl(&providerStaking)
	coin := sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(amt))
	d := s.delegator()
	v := s.validator(val)
	msg := stakingtypes.NewMsgDelegate(d, v, coin)
	_, err := server.Delegate(sdk.WrapSDKContext(s.ctx(P)), msg)
	// There may or may not be an error, depending on the trace
	_ = err
}

// undelegate undelegates amt tokens from validator val
func (s *Driver) undelegate(val, amt int64) {
	providerStaking := s.providerStakingKeeper()
	server := stakingkeeper.NewMsgServerImpl(&providerStaking)
	coin := sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(amt))
	d := s.delegator()
	v := s.validator(val)
	msg := stakingtypes.NewMsgUndelegate(d, v, coin)
	_, err := server.Undelegate(sdk.WrapSDKContext(s.ctx(P)), msg)
	// There may or may not be an error, depending on the trace
	_ = err
	providerStaking.GetAllDelegations(s.ctx(P))
}

// consumerSlash simulates a slash event occurring on the consumer chain.
// It can be for a downtime or doublesign.
func (s *Driver) consumerSlash(val sdk.ConsAddress, h int64, isDowntime bool, chain ChainId) {
	kind := stakingtypes.Infraction_INFRACTION_DOUBLE_SIGN
	if isDowntime {
		kind = stakingtypes.Infraction_INFRACTION_DOWNTIME
	}
	ctx := s.ctx(chain)
	before := len(ctx.EventManager().Events())
	s.consumerKeeper(chain).SlashWithInfractionReason(ctx, val, h, 0, sdk.Dec{}, kind)
	// consumer module emits packets on slash, so these must be collected.
	evts := ctx.EventManager().Events()
	packets := simibc.ParsePacketsFromEvents(evts[before:])
	if len(packets) > 0 {
		s.path(chain).Outboxes.AddPacket(string(chain), packets[0])
	}
}

func (s *Driver) updateClient(chain ChainId) {
	s.path(chain).UpdateClient(string(chain))
}

// deliver numPackets packets from the network to chain
func (s *Driver) deliver(chain ChainId, numPackets int) {
	// Makes sure client is updated
	s.updateClient(chain)
	// Deliver any outstanding acks
	s.path(chain).DeliverAcks(string(chain), 999999)
	// Consume deliverable packets from the network
	s.path(chain).DeliverPackets(string(chain), numPackets)
}

// packetQueue returns the queued packet sfrom sender to receiver,
// where either sender or receiver must be the provider.
func (s *Driver) packetQueue(sender ChainId, receiver ChainId) []simibc.Packet {
	var path *simibc.RelayedPath
	if sender == P {
		path = s.path(receiver)
	} else {
		path = s.path(sender)
	}
	outboxes := path.Outboxes
	outboxPackets := outboxes.OutboxPackets
	res, ok := outboxPackets[string(sender)]
	if !ok {
		return []simibc.Packet{}
	} else {
		return res
	}
}

func (s *Driver) getPacketsFromProviderToConsumer(consumer ChainId) []simibc.Packet {
	return s.path(consumer).Outboxes.OutboxPackets[string(consumer)]
}

func (s *Driver) getPacketsFromConsumerToProvider(consumer ChainId) []simibc.Packet {
	return s.path(consumer).Outboxes.OutboxPackets[P]
}

func (s *Driver) getStateString() string {
	var state strings.Builder

	state.WriteString("Provider\n")
	state.WriteString(s.getChainStateString("provider"))
	state.WriteString("\n")

	state.WriteString("Consumers Chains:\n")
	consumerChains := s.providerKeeper().GetAllConsumerChains(s.providerCtx())
	chainIds := make([]string, len(consumerChains))
	for i, consumerChain := range consumerChains {
		chainIds[i] = consumerChain.ChainId
	}
	state.WriteString(strings.Join(chainIds, ", "))
	state.WriteString("\n\n")

	for chain := range s.simibcs {
		state.WriteString(fmt.Sprintf("Chain %s\n", chain))
		state.WriteString(s.getChainStateString(chain))
		state.WriteString("\n")
	}

	return state.String()
}

func (s *Driver) isProviderChain(chain ChainId) bool {
	return chain == "provider"
}

func (s *Driver) getChainStateString(chain ChainId) string {
	ctx := s.ctx(chain)

	// Get the current block height
	height := ctx.BlockHeight()

	// Get the current block time
	blockTime := ctx.BlockTime()

	// Build the chain info string
	var chainInfo strings.Builder
	chainInfo.WriteString(fmt.Sprintf("  Height: %d\n", height))
	chainInfo.WriteString(fmt.Sprintf("  Time: %s\n", blockTime))

	if !s.isProviderChain(chain) {
		// Check whether the chain is in the consumer chains on the provider

		consumerChains := s.providerKeeper().GetAllConsumerChains(s.providerCtx())

		found := false
		for _, consumerChain := range consumerChains {
			if consumerChain.ChainId == string(chain) {
				found = true
			}
		}

		if found {
			chainInfo.WriteString("...is currently a consumer chain")
		} else {
			chainInfo.WriteString("...is currently not a consumer chain")
		}
	}

	// Build the validator info string
	var validatorInfo strings.Builder
	for index, valName := range s.valNames {
		var power int64
		if s.isProviderChain(chain) {
			power = s.providerPower(int64(index))
		} else {
			power, _ = s.consumerPower(int64(index), chain)
		}

		validatorInfo.WriteString(fmt.Sprintf("    Validator %s: power=%d\n", valName, power))
	}

	chainInfo.WriteString(validatorInfo.String())

	if !s.isProviderChain(chain) {
		var outboxInfo strings.Builder
		outboxInfo.WriteString("OutboxPackets:\n")

		outboxInfo.WriteString("OutgoingPackets: \n")
		outgoing := s.path(chain).Outboxes.OutboxPackets[string(chain)]
		for _, packet := range outgoing {
			outboxInfo.WriteString(fmt.Sprintf("%v\n", packet.Packet.String()))
		}

		outboxInfo.WriteString("IncomingPackets: \n")
		incoming := s.path(chain).Outboxes.OutboxPackets[P]
		for _, packet := range incoming {
			outboxInfo.WriteString(fmt.Sprintf("%v\n", packet.Packet.String()))
		}

		outboxInfo.WriteString("OutboxAcks:\n")

		outboxInfo.WriteString("OutgoingAcks: \n")
		outgoingAcks := s.path(chain).Outboxes.OutboxAcks[string(chain)]
		for _, packet := range outgoingAcks {
			outboxInfo.WriteString(fmt.Sprintf("%v\n", packet.Packet.String()))
		}

		outboxInfo.WriteString("IncomingAcks: \n")
		incomingAcks := s.path(chain).Outboxes.OutboxAcks[P]
		for _, packet := range incomingAcks {
			outboxInfo.WriteString(fmt.Sprintf("%v\n", packet.Packet.String()))
		}

		chainInfo.WriteString(outboxInfo.String())
	}

	return chainInfo.String()
}

// endAndBeginBlock ends the current block and begins a new one.
// After comitting, it processes any packets that have been sent by the chain,
// as witnessed by events, and adds them to the correct paths.
// It also updates the client header on the paths
// that involve the chain.
func (s *Driver) endAndBeginBlock(chain ChainId, timeAdvancement time.Duration) {
	testChain, found := s.coordinator.Chains[string(chain)]
	require.True(s.t, found, "chain %s not found", chain)

	header, packets := simibc.EndBlock(testChain, func() {})

	// for each packet, find the path it should be sent on
	for _, p := range packets {
		found := false
		for _, path := range s.simibcs {
			if path.PacketSentByChain(p, string(chain)) {
				path.Outboxes.AddPacket(string(chain), p)
				found = true
				break
			}
		}
		if !found {
			s.t.Fatal("packet does not belong to any path: ", p)
		}
	}

	for _, path := range s.simibcs {
		if path.InvolvesChain(string(chain)) {
			path.AddClientHeader(string(chain), header)
			path.Outboxes.Commit(string(chain))
		}
	}

	simibc.BeginBlock(testChain, timeAdvancement)

	for _, path := range s.simibcs {
		if path.InvolvesChain(string(chain)) {
			path.UpdateClient(path.Counterparty(string(chain)))
		}
	}
}

// DeliverPacketToConsumer delivers a packet from the provider to the given consumer recipient.
// It updates the client before delivering the packet.
// Since the channel is ordered, the packet that is delivered is the first packet in the outbox.
func (s *Driver) DeliverPacketToConsumer(recipient ChainId) {
	s.path(recipient).DeliverPackets(string(recipient), 1)
}

// DeliverPacketFromConsumer delivers a packet from the given consumer sender to the provider.
// It updates the client before delivering the packet.
// Since the channel is ordered, the packet that is delivered is the first packet in the outbox.
func (s *Driver) DeliverPacketFromConsumer(sender ChainId) {
	s.path(sender).DeliverPackets(P, 1) // deliver to the provider
}

// newDriver creates a new Driver object.
// It creates a new coordinator, but does not start any chains.
// The caller must call setupChains to start the chains and
// fully populate the Driver.
func newDriver(t *testing.T, validators []*cmttypes.Validator, valNames []string) *Driver {
	t.Log("Creating coordinator")
	coordinator := ibctesting.NewCoordinator(t, 0) // start without chains, which we add later

	suite := &Driver{
		t:           t,
		coordinator: coordinator,
		simibcs:     make(map[ChainId]*simibc.RelayedPath),
		validators:  validators,
		valNames:    valNames,
	}
	return suite
}
