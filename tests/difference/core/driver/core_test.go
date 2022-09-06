package core

import (
	"fmt"
	"math"
	"testing"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/stretchr/testify/suite"

	channelkeeper "github.com/cosmos/ibc-go/v3/modules/core/04-channel/keeper"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"

	stakingkeeper "github.com/cosmos/cosmos-sdk/x/staking/keeper"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	appProvider "github.com/cosmos/interchain-security/app/provider"

	simibc "github.com/cosmos/interchain-security/testutil/simibc"

	slashingkeeper "github.com/cosmos/cosmos-sdk/x/slashing/keeper"
	consumerkeeper "github.com/cosmos/interchain-security/x/ccv/consumer/keeper"
)

type CoreSuite struct {
	suite.Suite

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
	return b.providerChain().App.(*appProvider.App).StakingKeeper
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
func (s *CoreSuite) delegate(val int64, amt int64) {
	server := stakingkeeper.NewMsgServerImpl(s.providerStakingKeeper())
	coin := sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(amt))
	d := s.delegator()
	v := s.validator(val)
	msg := stakingtypes.NewMsgDelegate(d, v, coin)
	_, err := server.Delegate(sdk.WrapSDKContext(s.ctx(P)), msg)
	// There may or may not be an error, depending on the trace
	_ = err
}

// undelegate undelegates amt tokens from validator val
func (s *CoreSuite) undelegate(val int64, amt int64) {
	server := stakingkeeper.NewMsgServerImpl(s.providerStakingKeeper())
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
	kind := stakingtypes.DoubleSign
	if isDowntime {
		kind = stakingtypes.Downtime
	}
	ctx := s.ctx(C)
	before := len(ctx.EventManager().Events())
	s.consumerKeeper().Slash(ctx, val, h, 0, sdk.Dec{}, kind)
	// consumer module emits packets on slash, so these must be collected.
	evts := ctx.EventManager().ABCIEvents()
	for _, e := range evts[before:] {
		if e.Type == channeltypes.EventTypeSendPacket {
			packet, err := channelkeeper.ReconstructPacketFromEvent(e)
			s.Require().NoError(err)
			s.simibc.Link.AddPacket(s.chainID(C), packet)
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
	s.simibc.EndAndBeginBlock(s.chainID(chain), initState.BlockSeconds, func() {
		s.matchState()
	})
}

// matchState compares the state in the SUT to the state in the
// the model.
func (s *CoreSuite) matchState() {

	// Get a diagnostic for debugging
	diagnostic := s.traces.Diagnostic()
	chain := s.traces.Action().Chain

	// Model time, height start at 0 so we need an offset for comparisons.
	sutTimeOffset := time.Unix(s.offsetTimeUnix, 0).Add(-initState.BlockSeconds).UTC()
	modelTimeOffset := time.Duration(s.traces.Time()) * time.Second
	sutHeightOffset := s.offsetHeight - 1
	modelHeightOffset := int64(s.traces.Height())
	s.Require().Equalf(sutTimeOffset.Add(modelTimeOffset), s.time(chain), diagnostic+"%s Time mismatch", chain)
	s.Require().Equalf(sutHeightOffset+modelHeightOffset, s.height(chain), diagnostic+"%s Time mismatch", chain)
	if chain == P {
		for j := 0; j < initState.NumValidators; j++ {
			have := s.validatorStatus(int64(j))
			s.Require().Equalf(s.traces.Status(j), have, diagnostic+"P bond status mismatch for val %d, expect %s, have %s", j, s.traces.Status(j).String(), have.String())
		}
		for j := 0; j < initState.NumValidators; j++ {
			s.Require().Equalf(int64(s.traces.Tokens(j)), s.providerTokens(int64(j)), diagnostic+"P tokens mismatch for val %d", j)
		}
		// TODO: delegations
		s.Require().Equalf(int64(s.traces.DelegatorTokens()), s.delegatorBalance(), diagnostic+"P del balance mismatch")
		for j := 0; j < initState.NumValidators; j++ {
			s.Require().Equalf(s.traces.Jailed(j) != nil, s.isJailed(int64(j)), diagnostic+"P jail status mismatch for val %d", j)
		}
	}
	if chain == C {
		for j := 0; j < initState.NumValidators; j++ {
			exp := s.traces.ConsumerPower(j)
			actual, err := s.consumerPower(int64(j))
			if exp != nil {
				s.Require().Nilf(err, diagnostic+" validator not found")
				s.Require().Equalf(int64(*exp), actual, diagnostic+" power mismatch for val %d", j)
			} else {
				s.Require().Errorf(err, diagnostic+" power mismatch for val %d, expect 0 (nil), got %d", j, actual)
			}
		}
		// TODO: outstanding downtime
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

// TestAssumptions tests that the assumptions used to write the difftest
// driver hold. This test therefore does not test the system, but only that
// the driver is correctly setup.
func (s *CoreSuite) TestAssumptions() {

	const FAIL_MSG = "Assumptions for core diff test failed: there is a problem with the driver or how the test is setup."

	// Staking module maxValidators param is correct
	maxValsE := uint32(initState.MaxValidators)
	maxVals := s.providerStakingKeeper().GetParams(s.ctx(P)).MaxValidators

	if maxValsE != maxVals {
		s.T().Fatal(FAIL_MSG)
	}

	// Delegator balance is correct
	s.Require().Equal(int64(initState.InitialDelegatorTokens), s.delegatorBalance())

	// Slash factors are correct
	s.Require().Equal(initState.SlashDowntime, s.providerSlashingKeeper().SlashFractionDowntime(s.ctx(P)))
	s.Require().Equal(initState.SlashDoublesign, s.providerSlashingKeeper().SlashFractionDoubleSign(s.ctx(P)))

	// Provider unbonding period is correct
	stakeParams := s.providerStakingKeeper().GetParams(s.ctx(P))
	s.Require().Equal(stakeParams.UnbondingTime, initState.UnbondingP)
	// Consumer unbonding period is correct
	s.Require().Equal(s.consumerKeeper().UnbondingTime(s.ctx(C)), initState.UnbondingC)

	// Each validator has signing info
	for i := 0; i < len(initState.ValStates.Tokens); i++ {
		_, found := s.providerSlashingKeeper().GetValidatorSigningInfo(s.ctx(P), s.consAddr(int64(i)))
		if !found {
			s.Require().FailNow(FAIL_MSG)
		}
	}

	// Provider delegations are correct
	for i := 0; i < len(initState.ValStates.Delegation); i++ {
		E := int64(initState.ValStates.Delegation[i])
		A := s.delegation(int64(i))
		if E != A {
			s.T().Fatal(FAIL_MSG)
		}
	}

	// Provider validator tokens are correct
	for i := 0; i < len(initState.ValStates.Tokens); i++ {
		E := int64(initState.ValStates.Tokens[i])
		A := s.providerTokens(int64(i))
		if E != A {
			s.T().Fatal(FAIL_MSG)
		}
	}

	// Provider validator status is correct
	for i := 0; i < len(initState.ValStates.Status); i++ {
		E := initState.ValStates.Status[i]
		A := s.validatorStatus(int64(i))
		if E != A {
			s.T().Fatal(FAIL_MSG)
		}
	}

	// Staking module does not contain undelegations
	s.providerStakingKeeper().IterateUnbondingDelegations(s.ctx(P),
		func(index int64, ubd stakingtypes.UnbondingDelegation) bool {
			s.T().Fatal(FAIL_MSG)
			return false // Don't stop
		})

	// Staking module does contain redelegations
	s.providerStakingKeeper().IterateRedelegations(s.ctx(P),
		func(index int64, ubd stakingtypes.Redelegation) bool {
			s.T().Fatal(FAIL_MSG)
			return false // Don't stop
		})

	// Staking module does not contain unbonding validators
	endTime := time.Unix(math.MaxInt64, 0)
	endHeight := int64(math.MaxInt64)
	unbondingValIterator := s.providerStakingKeeper().ValidatorQueueIterator(s.ctx(P), endTime, endHeight)
	defer unbondingValIterator.Close()
	for ; unbondingValIterator.Valid(); unbondingValIterator.Next() {
		s.T().Fatal(FAIL_MSG)
	}

	// Consumer has no slash requests
	s.Require().Empty(s.consumerKeeper().GetPendingSlashRequests(s.ctx(C)))

	// Consumer has no maturities
	s.consumerKeeper().IteratePacketMaturityTime(s.ctx(C),
		func(vscId uint64, timeNs uint64) bool {
			s.T().Fatal(FAIL_MSG)
			return false // Don't stop
		})

	// Consumer power
	for i := 0; i < len(initState.ValStates.Status); i++ {
		expectFound := initState.ValStates.Status[i] == stakingtypes.Bonded
		expectPower := initState.ValStates.Tokens[i]
		addr := s.validator(int64(i))
		val, found := s.consumerKeeper().GetCCValidator(s.ctx(C), addr)
		s.Require().Equal(expectFound, found)
		if expectFound {
			if int64(expectPower) != val.Power {
				s.T().Fatal(FAIL_MSG)
			}
		}
	}

	// The offset time is the last committed time, but the SUT is +1 block ahead
	// because the currentHeader time is ahead of the last committed. Therefore sub
	// the difference (duration of 1 block).
	s.Require().Equal(int64(s.offsetTimeUnix), s.time(P).Add(-initState.BlockSeconds).Unix())
	s.Require().Equal(int64(s.offsetTimeUnix), s.time(C).Add(-initState.BlockSeconds).Unix())

	// The offset height is the last committed height, but the SUT is +1 because
	// the currentHeader is +1 ahead of the last committed. Therefore sub 1.
	s.Require().Equal(s.offsetHeight, s.height(P)-1)
	s.Require().Equal(s.offsetHeight, s.height(C)-1)

	// Network is empty
	s.Require().Empty(s.simibc.Link.OutboxPackets[P])
	s.Require().Empty(s.simibc.Link.OutboxPackets[C])
	s.Require().Empty(s.simibc.Link.OutboxAcks[P])
	s.Require().Empty(s.simibc.Link.OutboxAcks[C])
}

// Test a set of traces
func (s *CoreSuite) TestTraces() {
	s.traces = Traces{
		Data: LoadTraces("traces.json"),
	}
	// s.traces.Data = []TraceData{s.traces.Data[69]}
	for i := range s.traces.Data {
		s.Run(fmt.Sprintf("Trace num: %d", i), func() {
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
		})
	}
}

func TestCoreSuite(t *testing.T) {
	suite.Run(t, new(CoreSuite))
}

// SetupTest sets up the test suite in a 'zero' state which matches
// the initial state in the model.
func (s *CoreSuite) SetupTest() {
	state := initState
	path, valAddresses, offsetHeight, offsetTimeUnix := GetZeroState(&s.Suite, state)
	s.valAddresses = valAddresses
	s.offsetHeight = offsetHeight
	s.offsetTimeUnix = offsetTimeUnix
	s.simibc = simibc.MakeRelayedPath(s.Suite.T(), path)
}
