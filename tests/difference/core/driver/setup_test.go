package core

import (
	"math"
	"time"

	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
)

// TestAssumptionsSetup tests that the assumptions used to write the difftest
// driver hold. This test therefore does not test the system, but only that
// the driver is correctly setup.
func (s *CoreSuite) TestAssumptionsSetup() {

	const FAIL_MSG = "Assumptions for core diff test failed: there is a problem with the driver or how the test is setup."

	// Staking module maxValidators param is correct
	maxValsE := uint32(s.initState.MaxValidators)
	maxVals := s.providerStakingKeeper().GetParams(s.ctx(P)).MaxValidators

	if maxValsE != maxVals {
		s.T().Fatal(FAIL_MSG)
	}

	// TODO: Write a check to make sure that the slash throttle params are set correctly.
	// 		 The params should be set such that the slash throttle never kicks in and stop a slash.
	// 		 This is because the model assumes that a slash will always be executed, no matter
	// 		 how many. This can be achieve by setting the slash factor to e.g. 1.0 and the refresh
	// 		 period to 1 block.

	// Delegator balance is correct
	s.Require().Equal(int64(s.initState.InitialDelegatorTokens), s.delegatorBalance())

	// Slash factors are correct
	s.Require().Equal(s.initState.SlashDowntime, s.providerSlashingKeeper().SlashFractionDowntime(s.ctx(P)))
	s.Require().Equal(s.initState.SlashDoublesign, s.providerSlashingKeeper().SlashFractionDoubleSign(s.ctx(P)))

	// Provider unbonding period is correct
	stakeParams := s.providerStakingKeeper().GetParams(s.ctx(P))
	s.Require().Equal(stakeParams.UnbondingTime, s.initState.UnbondingP)
	// Consumer unbonding period is correct
	s.Require().Equal(s.consumerKeeper().UnbondingTime(s.ctx(C)), s.initState.UnbondingC)

	// Each validator has signing info
	for i := 0; i < len(s.initState.ValStates.Tokens); i++ {
		_, found := s.providerSlashingKeeper().GetValidatorSigningInfo(s.ctx(P), s.consAddr(int64(i)))
		if !found {
			s.Require().FailNow(FAIL_MSG)
		}
	}

	// Provider delegations are correct
	for i := 0; i < len(s.initState.ValStates.Delegation); i++ {
		E := int64(s.initState.ValStates.Delegation[i])
		A := s.delegation(int64(i))
		if E != A {
			s.T().Fatal(FAIL_MSG)
		}
	}

	// Provider validator tokens are correct
	for i := 0; i < len(s.initState.ValStates.Tokens); i++ {
		E := int64(s.initState.ValStates.Tokens[i])
		A := s.providerTokens(int64(i))
		if E != A {
			s.T().Fatal(FAIL_MSG)
		}
	}

	// Provider validator status is correct
	for i := 0; i < len(s.initState.ValStates.Status); i++ {
		E := s.initState.ValStates.Status[i]
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

	// Consumer has no pending data packets
	s.Require().Empty(s.consumerKeeper().GetPendingPackets(s.ctx(C)))

	// Consumer has no maturities
	for range s.consumerKeeper().GetAllPacketMaturityTimes(s.ctx(C)) {
		s.T().Fatal(FAIL_MSG)
	}

	// Consumer power
	for i := 0; i < len(s.initState.ValStates.Status); i++ {
		expectFound := s.initState.ValStates.Status[i] == stakingtypes.Bonded
		expectPower := s.initState.ValStates.Tokens[i]
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
	s.Require().Equal(int64(s.offsetTimeUnix), s.time(P).Add(-s.initState.BlockInterval).Unix())
	s.Require().Equal(int64(s.offsetTimeUnix), s.time(C).Add(-s.initState.BlockInterval).Unix())

	// The offset height is the last committed height, but the SUT is +1 because
	// the currentHeader is +1 ahead of the last committed. Therefore sub 1.
	s.Require().Equal(s.offsetHeight, s.height(P)-1)
	s.Require().Equal(s.offsetHeight, s.height(C)-1)

	// Network is empty
	s.Require().Empty(s.simibc.Outboxes.OutboxPackets[P])
	s.Require().Empty(s.simibc.Outboxes.OutboxPackets[C])
	s.Require().Empty(s.simibc.Outboxes.OutboxAcks[P])
	s.Require().Empty(s.simibc.Outboxes.OutboxAcks[C])
}
