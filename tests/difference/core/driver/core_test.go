package core

import (
	"fmt"
	"testing"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/stretchr/testify/suite"

	channeltypes "github.com/cosmos/ibc-go/v7/modules/core/04-channel/types"

	ibctestingcore "github.com/octopus-network/interchain-security/legacy_ibc_testing/core"
	ibctesting "github.com/octopus-network/interchain-security/legacy_ibc_testing/testing"

	stakingkeeper "github.com/cosmos/cosmos-sdk/x/staking/keeper"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	appConsumer "github.com/octopus-network/interchain-security/app/consumer"
	appProvider "github.com/octopus-network/interchain-security/app/provider"

	"github.com/octopus-network/interchain-security/testutil/simibc"

	slashingkeeper "github.com/cosmos/cosmos-sdk/x/slashing/keeper"

	consumerkeeper "github.com/octopus-network/interchain-security/x/ccv/consumer/keeper"
)

type CoreSuite struct {
	suite.Suite

	initState InitState

	// the current traces being executed
	traces Traces

	// simulate a relayed path
	simibc simibc.RelayedPath

	// keep around validators for easy access
	valAddresses []sdk.ValAddress

	// offsets: the model time and heights start at 0
	// so offsets are needed for comparisons.
	offsetTimeUnix int64
	offsetHeight   int64
}

// ctx returns the sdk.Context for the chain
func (s *CoreSuite) ctx(chain string) sdk.Context {
	return s.chain(chain).GetContext()
}

func (s *CoreSuite) chainID(chain string) string {
	return map[string]string{P: ibctesting.GetChainID(0), C: ibctesting.GetChainID(1)}[chain]
}

// chain returns the TestChain for a given chain identifier
func (s *CoreSuite) chain(chain string) *ibctesting.TestChain {
	return map[string]*ibctesting.TestChain{P: s.providerChain(), C: s.consumerChain()}[chain]
}

func (s *CoreSuite) providerChain() *ibctesting.TestChain {
	return s.simibc.Chain(ibctesting.GetChainID(0))
}

func (s *CoreSuite) consumerChain() *ibctesting.TestChain {
	return s.simibc.Chain(ibctesting.GetChainID(1))
}

func (b *CoreSuite) providerStakingKeeper() stakingkeeper.Keeper {
	return *b.providerChain().App.(*appProvider.App).StakingKeeper
}

func (b *CoreSuite) providerSlashingKeeper() slashingkeeper.Keeper {
	return b.providerChain().App.(*appProvider.App).SlashingKeeper
}

func (b *CoreSuite) consumerKeeper() consumerkeeper.Keeper {
	return b.consumerChain().App.(*appConsumer.App).ConsumerKeeper
}

// height returns the height of the current header of chain
func (s *CoreSuite) height(chain string) int64 {
	return s.chain(chain).CurrentHeader.GetHeight()
}

// time returns the time of the current header of chain
func (s *CoreSuite) time(chain string) time.Time {
	return s.chain(chain).CurrentHeader.Time
}

// delegator retrieves the address for the delegator account
func (s *CoreSuite) delegator() sdk.AccAddress {
	return s.providerChain().SenderAccount.GetAddress()
}

// validator returns the address for the validator with id (ix) i
func (s *CoreSuite) validator(i int64) sdk.ValAddress {
	return s.valAddresses[i]
}

// consAddr returns the ConsAdd for the validator with id (ix) i
func (s *CoreSuite) consAddr(i int64) sdk.ConsAddress {
	return sdk.ConsAddress(s.validator(i))
}

// isJailed returns the jail status of validator with id (ix) i
func (s *CoreSuite) isJailed(i int64) bool {
	val, found := s.providerStakingKeeper().GetValidator(s.ctx(P), s.validator(i))
	s.Require().Truef(found, "GetValidator() -> !found")
	return val.IsJailed()
}

// consumerPower returns the power on the consumer chain for
// validator with id (ix) i
func (s *CoreSuite) consumerPower(i int64) (int64, error) {
	v, found := s.consumerKeeper().GetCCValidator(s.ctx(C), s.validator(i))
	if !found {
		return 0, fmt.Errorf("GetCCValidator() -> !found")
	}
	return v.Power, nil
}

// delegation returns the number of delegated tokens in the delegation from
// the delegator account to the validator with id (ix) i
func (s *CoreSuite) delegation(i int64) int64 {
	d, found := s.providerStakingKeeper().GetDelegation(s.ctx(P), s.delegator(), s.validator(i))
	s.Require().Truef(found, "GetDelegation() -> !found")
	return d.Shares.TruncateInt64()
}

// validatorStatus returns the validator status for validator with id (ix) i
// on the provider chain
func (s *CoreSuite) validatorStatus(i int64) stakingtypes.BondStatus {
	v, found := s.providerStakingKeeper().GetValidator(s.ctx(P), s.validator(i))
	s.Require().Truef(found, "GetValidator() -> !found")
	return v.GetStatus()
}

// providerTokens returns the number of tokens that the validator with
// id (ix) i has delegated to it in total on the provider chain
func (s *CoreSuite) providerTokens(i int64) int64 {
	v, found := s.providerStakingKeeper().GetValidator(s.ctx(P), s.validator(i))
	s.Require().Truef(found, "GetValidator() -> !found")
	return v.Tokens.Int64()
}

// delegatorBalance returns the balance of the delegator account
func (s *CoreSuite) delegatorBalance() int64 {
	d := s.delegator()
	bal := s.providerChain().App.(*appProvider.App).BankKeeper.GetBalance(s.ctx(P), d, sdk.DefaultBondDenom)
	return bal.Amount.Int64()
}

// delegate delegates amt tokens to validator val
func (s *CoreSuite) delegate(val, amt int64) {
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
func (s *CoreSuite) undelegate(val, amt int64) {
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
func (s *CoreSuite) consumerSlash(val sdk.ConsAddress, h int64, isDowntime bool) {
	kind := stakingtypes.Infraction_INFRACTION_DOUBLE_SIGN
	if isDowntime {
		kind = stakingtypes.Infraction_INFRACTION_DOWNTIME
	}
	ctx := s.ctx(C)
	before := len(ctx.EventManager().Events())
	s.consumerKeeper().SlashWithInfractionReason(ctx, val, h, 0, sdk.Dec{}, kind)
	// consumer module emits packets on slash, so these must be collected.
	evts := ctx.EventManager().ABCIEvents()
	for _, e := range evts[before:] {
		if e.Type == channeltypes.EventTypeSendPacket {
			packet, err := ibctestingcore.ReconstructPacketFromEvent(e)
			s.Require().NoError(err)
			s.simibc.Outboxes.AddPacket(s.chainID(C), packet)
		}
	}
}

func (s *CoreSuite) updateClient(chain string) {
	s.simibc.UpdateClient(s.chainID(chain))
}

// deliver numPackets packets from the network to chain
func (s *CoreSuite) deliver(chain string, numPackets int) {
	// Makes sure client is updated
	s.updateClient(chain)
	// Deliver any outstanding acks
	s.simibc.DeliverAcks(s.chainID(chain), 999999)
	// Consume deliverable packets from the network
	s.simibc.DeliverPackets(s.chainID(chain), numPackets)
}

func (s *CoreSuite) endAndBeginBlock(chain string) {
	s.simibc.EndAndBeginBlock(s.chainID(chain), s.initState.BlockInterval, func() {
		s.compareModelAndSystemState()
	})
}

// compareModelAndSystemState compares the state in the SUT to the state in the
// the model.
func (s *CoreSuite) compareModelAndSystemState() {
	// Get a diagnostic for debugging
	diagnostic := s.traces.Diagnostic()
	chain := s.traces.Action().Chain

	// Model time, height start at 0 so we need an offset for comparisons.
	sutTimeOffset := time.Unix(s.offsetTimeUnix, 0).Add(-s.initState.BlockInterval).UTC()
	modelTimeOffset := time.Duration(s.traces.Time()) * time.Second
	sutHeightOffset := s.offsetHeight - 1
	modelHeightOffset := int64(s.traces.Height())
	s.Require().Equalf(sutTimeOffset.Add(modelTimeOffset), s.time(chain), diagnostic+"%s Time mismatch", chain)
	s.Require().Equalf(sutHeightOffset+modelHeightOffset, s.height(chain), diagnostic+"%s Time mismatch", chain)
	if chain == P {
		for j := 0; j < s.initState.NumValidators; j++ {
			have := s.validatorStatus(int64(j))
			s.Require().Equalf(s.traces.Status(j), have, diagnostic+"P bond status mismatch for val %d, expect %s, have %s", j, s.traces.Status(j).String(), have.String())
		}
		for j := 0; j < s.initState.NumValidators; j++ {
			s.Require().Equalf(int64(s.traces.Tokens(j)), s.providerTokens(int64(j)), diagnostic+"P tokens mismatch for val %d", j)
		}
		s.Require().Equalf(int64(s.traces.DelegatorTokens()), s.delegatorBalance(), diagnostic+"P del balance mismatch")
		for j := 0; j < s.initState.NumValidators; j++ {
			a := s.traces.Jailed(j) != nil
			b := s.isJailed(int64(j))
			s.Require().Equalf(a, b, diagnostic+"P jail status mismatch for val %d", j)
		}
	}
	if chain == C {
		for j := 0; j < s.initState.NumValidators; j++ {
			exp := s.traces.ConsumerPower(j)
			actual, err := s.consumerPower(int64(j))
			if exp != nil {
				s.Require().Nilf(err, diagnostic+" validator not found")
				s.Require().Equalf(int64(*exp), actual, diagnostic+" power mismatch for val %d", j)
			} else {
				s.Require().Errorf(err, diagnostic+" power mismatch for val %d, expect 0 (nil), got %d", j, actual)
			}
		}
	}
}

func (s *CoreSuite) executeTrace() {
	for i := range s.traces.Actions() {
		s.traces.CurrentActionIx = i

		a := s.traces.Action()

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
		case "ConsumerSlash":
			s.consumerSlash(
				s.consAddr(int64(a.Val)),
				// The SUT height is greater than the model height
				// because the SUT has to do initialization.
				int64(a.InfractionHeight)+s.offsetHeight,
				a.IsDowntime,
			)
		case "UpdateClient":
			s.updateClient(a.Chain)
		case "Deliver":
			s.deliver(a.Chain, a.NumPackets)
		case "EndAndBeginBlock":
			s.endAndBeginBlock(a.Chain)
		default:
			s.Require().FailNow("Failed to parse action")
		}
	}
}

// Test a set of traces
func (s *CoreSuite) TestTraces() {
	s.traces = Traces{
		Data: LoadTraces("traces.json"),
	}
	shortest := -1
	shortestLen := 10000000000
	for i := range s.traces.Data {
		if !s.Run(fmt.Sprintf("Trace ix: %d", i), func() {
			// Setup a new pair of chains for each trace
			s.SetupTest()

			s.traces.CurrentTraceIx = i
			defer func() {
				// If a panic occurs, we trap it to print a diagnostic
				// and improve debugging experience.
				if r := recover(); r != nil {
					fmt.Println(s.traces.Diagnostic())
					fmt.Println(r)
					// Double panic to halt.
					panic("Panic occurred during TestTraces")
				}
			}()
			// Record information about the trace, for debugging
			// diagnostics.
			s.executeTrace()
		}) {
			if s.traces.CurrentActionIx < shortestLen {
				shortest = s.traces.CurrentTraceIx
				shortestLen = s.traces.CurrentActionIx
			}
		}
	}
	fmt.Println("Shortest [traceIx, actionIx]:", shortest, shortestLen)
}

func TestCoreSuite(t *testing.T) {
	suite.Run(t, new(CoreSuite))
}

// SetupTest sets up the test suite in a 'zero' state which matches
// the initial state in the model.
func (s *CoreSuite) SetupTest() {
	path, valAddresses, offsetHeight, offsetTimeUnix := GetZeroState(&s.Suite, initStateVar)
	s.initState = initStateVar
	s.valAddresses = valAddresses
	s.offsetHeight = offsetHeight
	s.offsetTimeUnix = offsetTimeUnix
	s.simibc = simibc.MakeRelayedPath(s.Suite.T(), path)
}
