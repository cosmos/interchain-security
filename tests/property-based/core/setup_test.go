package core

import (
	"math"
	"testing"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/stretchr/testify/assert"

	ibctesting "github.com/cosmos/interchain-security/legacy_ibc_testing/testing"

	stakingkeeper "github.com/cosmos/cosmos-sdk/x/staking/keeper"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	appProvider "github.com/cosmos/interchain-security/app/provider"

	simibc "github.com/cosmos/interchain-security/testutil/simibc"

	slashingkeeper "github.com/cosmos/cosmos-sdk/x/slashing/keeper"
	consumerkeeper "github.com/cosmos/interchain-security/x/ccv/consumer/keeper"
)

type AssumptionsHelper struct {
	t *testing.T

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
func (s *AssumptionsHelper) ctx(chain string) sdk.Context {
	return s.chain(chain).GetContext()
}

// chain returns the TestChain for a given chain identifier
func (s *AssumptionsHelper) chain(chain string) *ibctesting.TestChain {
	return map[string]*ibctesting.TestChain{P: s.providerChain(), C: s.consumerChain()}[chain]
}

func (s *AssumptionsHelper) providerChain() *ibctesting.TestChain {
	return s.simibc.Chain(ibctesting.GetChainID(0))
}

func (s *AssumptionsHelper) consumerChain() *ibctesting.TestChain {
	return s.simibc.Chain(ibctesting.GetChainID(1))
}

func (b *AssumptionsHelper) providerStakingKeeper() stakingkeeper.Keeper {
	return b.providerChain().App.(*appProvider.App).StakingKeeper
}

func (b *AssumptionsHelper) providerSlashingKeeper() slashingkeeper.Keeper {
	return b.providerChain().App.(*appProvider.App).SlashingKeeper
}

func (b *AssumptionsHelper) consumerKeeper() consumerkeeper.Keeper {
	return b.consumerChain().App.(*appConsumer.App).ConsumerKeeper
}

// height returns the height of the current header of chain
func (s *AssumptionsHelper) height(chain string) int64 {
	return s.chain(chain).CurrentHeader.GetHeight()
}

// time returns the time of the current header of chain
func (s *AssumptionsHelper) time(chain string) time.Time {
	return s.chain(chain).CurrentHeader.Time
}

// delegator retrieves the address for the delegator account
func (s *AssumptionsHelper) delegator() sdk.AccAddress {
	return s.providerChain().SenderAccount.GetAddress()
}

// validator returns the address for the validator with id (ix) i
func (s *AssumptionsHelper) validator(i int64) sdk.ValAddress {
	return s.valAddresses[i]
}

// consAddr returns the ConsAdd for the validator with id (ix) i
func (s *AssumptionsHelper) consAddr(i int64) sdk.ConsAddress {
	return sdk.ConsAddress(s.validator(i))
}

// delegation returns the number of delegated tokens in the delegation from
// the delegator account to the validator with id (ix) i
func (s *AssumptionsHelper) delegation(i int64) int64 {
	d, found := s.providerStakingKeeper().GetDelegation(s.ctx(P), s.delegator(), s.validator(i))
	assert.Truef(s.t, found, "GetDelegation() -> !found")
	return d.Shares.TruncateInt64()
}

// validatorStatus returns the validator status for validator with id (ix) i
// on the provider chain
func (s *AssumptionsHelper) validatorStatus(i int64) stakingtypes.BondStatus {
	v, found := s.providerStakingKeeper().GetValidator(s.ctx(P), s.validator(i))
	assert.Truef(s.t, found, "GetValidator() -> !found")
	return v.GetStatus()
}

// providerTokens returns the number of tokens that the validator with
// id (ix) i has delegated to it in total on the provider chain
func (s *AssumptionsHelper) providerTokens(i int64) int64 {
	v, found := s.providerStakingKeeper().GetValidator(s.ctx(P), s.validator(i))
	assert.Truef(s.t, found, "GetValidator() -> !found")
	return v.Tokens.Int64()
}

// delegatorBalance returns the balance of the delegator account
func (s *AssumptionsHelper) delegatorBalance() int64 {
	d := s.delegator()
	bal := s.providerChain().App.(*appProvider.App).BankKeeper.GetBalance(s.ctx(P), d, sdk.DefaultBondDenom)
	return bal.Amount.Int64()
}

// TestAssumptions tests that the assumptions used to write the difftest
// driver hold. This test therefore does not test the system, but only that
// the driver is correctly setup.
func TestAssumptions(t *testing.T) {
	s := AssumptionsHelper{}
	s.t = t
	state := initState
	z := GetZeroState(t, state)

	s.valAddresses = z.addrs
	s.offsetHeight = z.heightLastCommit
	s.offsetTimeUnix = z.timeLastCommit.Unix()
	s.simibc = simibc.MakeRelayedPath(s.t, z.path)

	const FAIL_MSG = "Assumptions for core diff test failed: there is a problem with the driver or how the test is setup."

	// Staking module maxValidators param is correct
	maxValsE := uint32(initState.MaxValidators)
	maxVals := s.providerStakingKeeper().GetParams(s.ctx(P)).MaxValidators

	if maxValsE != maxVals {
		s.t.Fatal(FAIL_MSG)
	}

	// TODO: Write a check to make sure that the slash throttle params are set correctly.
	// 		 The params should be set such that the slash throttle never kicks in and stop a slash.
	// 		 This is because the model assumes that a slash will always be executed, no matter
	// 		 how many. This can be achieve by setting the slash factor to e.g. 1.0 and the refresh
	// 		 period to 1 block.

	// Delegator balance is correct
	assert.Equal(s.t, int64(initState.InitialDelegatorTokens), s.delegatorBalance())

	// Slash factors are correct
	assert.Equal(s.t, initState.SlashDowntime, s.providerSlashingKeeper().SlashFractionDowntime(s.ctx(P)))
	assert.Equal(s.t, initState.SlashDoublesign, s.providerSlashingKeeper().SlashFractionDoubleSign(s.ctx(P)))

	// Provider unbonding period is correct
	stakeParams := s.providerStakingKeeper().GetParams(s.ctx(P))
	assert.Equal(s.t, stakeParams.UnbondingTime, initState.UnbondingP)
	// Consumer unbonding period is correct
	assert.Equal(s.t, s.consumerKeeper().UnbondingTime(s.ctx(C)), initState.UnbondingC)

	// Each validator has signing info
	for i := 0; i < len(initState.ValStates.Tokens); i++ {
		_, found := s.providerSlashingKeeper().GetValidatorSigningInfo(s.ctx(P), s.consAddr(int64(i)))
		if !found {
			s.t.Fatal(FAIL_MSG)
		}
	}

	// Provider delegations are correct
	for i := 0; i < len(initState.ValStates.Delegation); i++ {
		E := int64(initState.ValStates.Delegation[i])
		A := s.delegation(int64(i))
		if E != A {
			s.t.Fatal(FAIL_MSG)
		}
	}

	// Provider validator tokens are correct
	for i := 0; i < len(initState.ValStates.Tokens); i++ {
		E := int64(initState.ValStates.Tokens[i])
		A := s.providerTokens(int64(i))
		if E != A {
			s.t.Fatal(FAIL_MSG)
		}
	}

	// Provider validator status is correct
	for i := 0; i < len(initState.ValStates.Status); i++ {
		E := initState.ValStates.Status[i]
		A := s.validatorStatus(int64(i))
		if E != A {
			s.t.Fatal(FAIL_MSG)
		}
	}

	// Staking module does not contain undelegations
	s.providerStakingKeeper().IterateUnbondingDelegations(s.ctx(P),
		func(index int64, ubd stakingtypes.UnbondingDelegation) bool {
			s.t.Fatal(FAIL_MSG)
			return false // Don't stop
		})

	// Staking module does contain redelegations
	s.providerStakingKeeper().IterateRedelegations(s.ctx(P),
		func(index int64, ubd stakingtypes.Redelegation) bool {
			s.t.Fatal(FAIL_MSG)
			return false // Don't stop
		})

	// Staking module does not contain unbonding validators
	endTime := time.Unix(math.MaxInt64, 0)
	endHeight := int64(math.MaxInt64)
	unbondingValIterator := s.providerStakingKeeper().ValidatorQueueIterator(s.ctx(P), endTime, endHeight)
	defer unbondingValIterator.Close()
	for ; unbondingValIterator.Valid(); unbondingValIterator.Next() {
		s.t.Fatal(FAIL_MSG)
	}

	// Consumer has no pending data packets
	assert.Empty(s.t, s.consumerKeeper().GetPendingPackets(s.ctx(C)))

	// Consumer has no maturities
	for range s.consumerKeeper().GetAllPacketMaturityTimes(s.ctx(C)) {
		s.t.Fatal(FAIL_MSG)
	}

	// Consumer power
	for i := 0; i < len(initState.ValStates.Status); i++ {
		expectFound := initState.ValStates.Status[i] == stakingtypes.Bonded
		expectPower := initState.ValStates.Tokens[i]
		addr := s.validator(int64(i))
		val, found := s.consumerKeeper().GetCCValidator(s.ctx(C), addr)
		assert.Equal(s.t, expectFound, found)
		if expectFound {
			if int64(expectPower) != val.Power {
				s.t.Fatal(FAIL_MSG)
			}
		}
	}

	// The offset time is the last committed time, but the SUT is +1 block ahead
	// because the currentHeader time is ahead of the last committed. Therefore sub
	// the difference (duration of 1 block).
	assert.Equal(s.t, int64(s.offsetTimeUnix), s.time(P).Add(-initState.BlockInterval).Unix())
	assert.Equal(s.t, int64(s.offsetTimeUnix), s.time(C).Add(-initState.BlockInterval).Unix())

	// The offset height is the last committed height, but the SUT is +1 because
	// the currentHeader is +1 ahead of the last committed. Therefore sub 1.
	assert.Equal(s.t, s.offsetHeight, s.height(P)-1)
	assert.Equal(s.t, s.offsetHeight, s.height(C)-1)

	// Network is empty
	assert.Empty(s.t, s.simibc.Link.OutboxPackets[P])
	assert.Empty(s.t, s.simibc.Link.OutboxPackets[C])
	assert.Empty(s.t, s.simibc.Link.OutboxAcks[P])
	assert.Empty(s.t, s.simibc.Link.OutboxAcks[C])
}
