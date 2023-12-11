package main

import (
	"fmt"
	"log"
	"math"
	"strings"
	"testing"
	"time"

	channeltypes "github.com/cosmos/ibc-go/v7/modules/core/04-channel/types"
	tendermint "github.com/cosmos/ibc-go/v7/modules/light-clients/07-tendermint"
	ibctesting "github.com/cosmos/ibc-go/v7/testing"
	"github.com/stretchr/testify/require"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingkeeper "github.com/cosmos/cosmos-sdk/x/staking/keeper"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	abcitypes "github.com/cometbft/cometbft/abci/types"
	cmttypes "github.com/cometbft/cometbft/types"

	appConsumer "github.com/cosmos/interchain-security/v3/app/consumer"
	appProvider "github.com/cosmos/interchain-security/v3/app/provider"
	simibc "github.com/cosmos/interchain-security/v3/testutil/simibc"
	consumerkeeper "github.com/cosmos/interchain-security/v3/x/ccv/consumer/keeper"
	consumertypes "github.com/cosmos/interchain-security/v3/x/ccv/consumer/types"
	providerkeeper "github.com/cosmos/interchain-security/v3/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
)

// Define a new type for ChainIds to be more explicit
// about what the string represents.
type ChainId string

type ModelParams struct {
	VscTimeout              time.Duration
	CcvTimeout              map[ChainId]time.Duration
	UnbondingPeriodPerChain map[ChainId]time.Duration
	TrustingPeriodPerChain  map[ChainId]time.Duration
	MaxClockDrift           time.Duration
}

type Driver struct {
	t *testing.T

	coordinator *ibctesting.Coordinator

	// simulate IBC network: for each consumer chain name, we have a path between consumer and provider
	simibcs map[ChainId]*simibc.RelayedPath

	// keep around validators for easy access
	validators []*cmttypes.Validator
	valNames   []string

	DriverStats *Stats
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

func (b *Driver) consumerKeeper(chain ChainId) consumerkeeper.Keeper {
	return b.chain(chain).App.(*appConsumer.App).ConsumerKeeper
}

// runningTime returns the timestamp of the current header of chain
func (s *Driver) runningTime(chain ChainId) time.Time {
	testChain := s.chain(chain)
	return testChain.CurrentHeader.Time
}

// lastTime returns the timestamp of the last header of chain
func (s *Driver) lastTime(chain ChainId) time.Time {
	testChain := s.chain(chain)
	return testChain.LastHeader.Header.Time
}

// delegator retrieves the address for the delegator account
func (s *Driver) delegator() sdk.AccAddress {
	return s.providerChain().SenderAccount.GetAddress()
}

// validator returns the address for the validator with id (ix) i
func (s *Driver) validator(i int64) sdk.ValAddress {
	return sdk.ValAddress(s.validators[i].Address)
}

// consumerPower returns the power on the consumer chain chain for
// the validator with index i
func (s *Driver) consumerPower(i int64, chain ChainId) (int64, error) {
	v, found := s.consumerKeeper(chain).GetCCValidator(s.ctx(chain), s.validator(i))
	if !found {
		return 0, fmt.Errorf("validator %v not found", s.validator(i))
	}
	return v.Power, nil
}

// consumerTokens returns the number of tokens that the validator with
// id (ix) i has delegated to it in total on the provider chain
func (s *Driver) providerPower(i int64) (int64, error) {
	v, found := s.providerStakingKeeper().GetValidator(s.ctx(PROVIDER), s.validator(i))
	if !found {
		return 0, fmt.Errorf("validator with id %v not found on provider", i)
	} else {
		return v.BondedTokens().Int64(), nil
	}
}

func (s *Driver) providerValidatorSet() []stakingtypes.Validator {
	return s.providerStakingKeeper().GetAllValidators(s.ctx(PROVIDER))
}

func (s *Driver) consumerValidatorSet(chain ChainId) []consumertypes.CrossChainValidator {
	return s.consumerKeeper(chain).GetAllCCValidator(s.ctx(chain))
}

// delegate delegates amt tokens to validator val
func (s *Driver) delegate(val, amt int64) {
	providerStaking := s.providerStakingKeeper()
	server := stakingkeeper.NewMsgServerImpl(&providerStaking)
	coin := sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(amt))
	d := s.delegator()
	v := s.validator(val)
	msg := stakingtypes.NewMsgDelegate(d, v, coin)
	server.Delegate(sdk.WrapSDKContext(s.ctx(PROVIDER)), msg)
}

// undelegate undelegates amt tokens from validator val
func (s *Driver) undelegate(val, amt int64) {
	providerStaking := s.providerStakingKeeper()
	server := stakingkeeper.NewMsgServerImpl(&providerStaking)
	coin := sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(amt))
	d := s.delegator()
	v := s.validator(val)
	msg := stakingtypes.NewMsgUndelegate(d, v, coin)
	server.Undelegate(sdk.WrapSDKContext(s.ctx(PROVIDER)), msg)
}

// packetQueue returns the queued packets from sender to receiver,
// where either sender or receiver must be the provider.
func (s *Driver) packetQueue(sender, receiver ChainId) []simibc.Packet {
	var path *simibc.RelayedPath
	if sender == PROVIDER {
		path = s.path(receiver)
	} else {
		if receiver != PROVIDER {
			log.Fatalf("either receiver '%v' or sender '%v' should be provider '%v', but neither is", sender, receiver, PROVIDER)
		}
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
	return chain == PROVIDER
}

func (s *Driver) getChainStateString(chain ChainId) string {
	ctx := s.ctx(chain)

	// Get the current block height
	height := ctx.BlockHeight()

	// Get the current block time
	runningTime := s.runningTime(chain)

	// get the time of the last block
	lastTime := s.lastTime(chain)

	// Build the chain info string
	var chainInfo strings.Builder
	chainInfo.WriteString(fmt.Sprintf("  Height: %d\n", height))
	chainInfo.WriteString(fmt.Sprintf("  Running Time: %s\n", runningTime))
	chainInfo.WriteString(fmt.Sprintf("  Last Time entered on chain: %s\n", lastTime))

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
			power, _ = s.providerPower(int64(index))
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
		incoming := s.path(chain).Outboxes.OutboxPackets[PROVIDER]
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
		incomingAcks := s.path(chain).Outboxes.OutboxAcks[PROVIDER]
		for _, packet := range incomingAcks {
			outboxInfo.WriteString(fmt.Sprintf("%v\n", packet.Packet.String()))
		}

		chainInfo.WriteString(outboxInfo.String())
	}

	return chainInfo.String()
}

// endAndBeginBlock ends the current block and begins a new one.
// After committing, it processes any packets that have been sent by the chain,
// as witnessed by events, and adds them to the correct paths.
// It also updates the client header on the paths
// that involve the chain.
// Returns the header of the chain.
func (s *Driver) endAndBeginBlock(chain ChainId, timeAdvancement time.Duration) *tendermint.Header {
	testChain, found := s.coordinator.Chains[string(chain)]
	require.True(s.t, found, "chain %s not found", chain)

	header, packets := simibc.EndBlock(testChain, func() {})

	s.DriverStats.numSentPackets += len(packets)
	s.DriverStats.numBlocks += 1
	s.DriverStats.totalBlockTimePassedPerTrace += timeAdvancement

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
			path.Outboxes.Commit(string(chain))
		}
	}

	simibc.BeginBlock(testChain, timeAdvancement)
	return header
}

func (s *Driver) runningConsumers() []providertypes.Chain {
	// consumers that are still consumers on the provider
	consumersOnProvider := s.providerKeeper().GetAllConsumerChains(s.providerCtx())

	consumersWithIntactChannel := make([]providertypes.Chain, 0)
	for _, consumer := range consumersOnProvider {
		if s.path(ChainId(consumer.ChainId)).Path.EndpointA.GetChannel().State == channeltypes.CLOSED ||
			s.path(ChainId(consumer.ChainId)).Path.EndpointB.GetChannel().State == channeltypes.CLOSED {
			continue
		}
		consumersWithIntactChannel = append(consumersWithIntactChannel, consumer)
	}
	return consumersWithIntactChannel
}

func (s *Driver) setTime(chain ChainId, newTime time.Time) {
	testChain, found := s.coordinator.Chains[string(chain)]
	require.True(s.t, found, "chain %s not found", chain)

	testChain.CurrentHeader.Time = newTime
	testChain.App.BeginBlock(abcitypes.RequestBeginBlock{Header: testChain.CurrentHeader})
}

// DeliverPacketToConsumer delivers a packet from the provider to the given consumer recipient.
// It updates the client before delivering the packet.
// Since the channel is ordered, the packet that is delivered is the first packet in the outbox.
func (s *Driver) DeliverPacketToConsumer(recipient ChainId, expectError bool) {
	s.path(recipient).DeliverPackets(string(recipient), 1, expectError)
}

// DeliverPacketFromConsumer delivers a packet from the given consumer sender to the provider.
// It updates the client before delivering the packet.
// Since the channel is ordered, the packet that is delivered is the first packet in the outbox.
func (s *Driver) DeliverPacketFromConsumer(sender ChainId, expectError bool) {
	s.path(sender).DeliverPackets(PROVIDER, 1, expectError) // deliver to the provider
}

// DeliverAcks delivers, for each path,
// all possible acks (up to math.MaxInt many per path).
func (s *Driver) DeliverAcks() {
	for _, chain := range s.runningConsumers() {
		path := s.path(ChainId(chain.ChainId))
		path.DeliverAcks(path.Path.EndpointA.Chain.ChainID, math.MaxInt)
		path.DeliverAcks(path.Path.EndpointB.Chain.ChainID, math.MaxInt)
	}
}

// stopConsumer stops a given consumer chain.
func (s *Driver) stopConsumer(chain ChainId) error {
	// stop the consumer chain on the provider
	return s.providerKeeper().StopConsumerChain(s.providerCtx(), string(chain), true)
}

// newDriver creates a new Driver object.
// It creates a new coordinator, but does not start any chains.
// The caller must call setupChains to start the chains and
// fully populate the Driver.
func newDriver(t *testing.T, validators []*cmttypes.Validator, valNames []string) *Driver {
	t.Helper()
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
