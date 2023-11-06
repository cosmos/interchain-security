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

	appConsumer "github.com/cosmos/interchain-security/v3/app/consumer"
	appProvider "github.com/cosmos/interchain-security/v3/app/provider"

	simibc "github.com/cosmos/interchain-security/v3/testutil/simibc"
	consumerkeeper "github.com/cosmos/interchain-security/v3/x/ccv/consumer/keeper"
	providerkeeper "github.com/cosmos/interchain-security/v3/x/ccv/provider/keeper"
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
	valAddresses []sdk.ValAddress
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
	return s.valAddresses[i]
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
	v, found := s.consumerKeeper(chain).GetCCValidator(s.ctx(C), s.validator(i))
	if !found {
		return 0, fmt.Errorf("GetCCValidator(%v) -> !found", s.validator(i))
	}
	return v.Power, nil
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
	require.True(s.t, found, "GetValidator(%v) -> !found", s.validator(i))
	return v.Tokens.Int64()
}

func (s *Driver) validatorSet(chain ChainId) []stakingtypes.Validator {
	if chain == P {
		return s.providerStakingKeeper().GetAllValidators(s.ctx(P))
	} else {
		return s.consumerKeeper(chain).GetAllValidators(s.ctx(chain))
	}
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
}

// consumerSlash simulates a slash event occurring on the consumer chain.
// It can be for a downtime or doublesign.
func (s *Driver) consumerSlash(val sdk.ConsAddress, h int64, isDowntime bool, chain ChainId) {
	kind := stakingtypes.Infraction_INFRACTION_DOUBLE_SIGN
	if isDowntime {
		kind = stakingtypes.Infraction_INFRACTION_DOWNTIME
	}
	ctx := s.ctx(C)
	before := len(ctx.EventManager().Events())
	s.consumerKeeper(chain).SlashWithInfractionReason(ctx, val, h, 0, sdk.Dec{}, kind)
	// consumer module emits packets on slash, so these must be collected.
	evts := ctx.EventManager().Events()
	packets := simibc.ParsePacketsFromEvents(evts[before:])
	if len(packets) > 0 {
		s.path(chain).Outboxes.AddPacket(C, packets[0])
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

func (s *Driver) getStateString() string {
	var state strings.Builder

	state.WriteString("Provider\n")
	state.WriteString(s.getChainStateString("provider"))
	state.WriteString("\n")

	for chain := range s.simibcs {
		state.WriteString(fmt.Sprintf("Chain %s\n", chain))
		state.WriteString(s.getChainStateString(chain))
		state.WriteString("\n")
	}

	return state.String()
}

func (s *Driver) getChainStateString(chain ChainId) string {
	ctx := s.ctx(chain)

	// Get the current block height
	height := ctx.BlockHeight()

	// Get the current block time
	blockTime := ctx.BlockTime()

	// Get the validator set for the current block
	validatorSet := s.validatorSet(chain)

	// Build the chain info string
	var chainInfo strings.Builder
	chainInfo.WriteString(fmt.Sprintf("  Height: %d\n", height))
	chainInfo.WriteString(fmt.Sprintf("  Time: %s\n", blockTime))

	// Build the validator info string
	var validatorInfo strings.Builder
	for _, validator := range validatorSet {
		validatorInfo.WriteString(fmt.Sprintf("    Validator %s: power=%d\n", validator.GetOperator().String(), validator.BondedTokens()))
	}

	chainInfo.WriteString(validatorInfo.String())

	return chainInfo.String()
}

func (s *Driver) endAndBeginBlock(chain ChainId, timeAdvancement time.Duration, preCommitCallback func()) {
	s.path(chain).EndAndBeginBlock(string(chain), timeAdvancement, func() {
	})
}

func newDriver(t *testing.T, valAddresses []sdk.ValAddress) *Driver {
	t.Log("Creating coordinator")
	coordinator := ibctesting.NewCoordinator(t, 0) // start without chains, which we add later

	suite := &Driver{
		t:            t,
		coordinator:  coordinator,
		simibcs:      make(map[ChainId]*simibc.RelayedPath),
		valAddresses: valAddresses,
	}
	return suite
}
