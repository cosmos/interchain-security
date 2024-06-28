package integration

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
)

// TestUndelegationCompletion tests that undelegations complete after
// the unbonding period elapses on the provider, regardless of the consumer's state
func (s *CCVTestSuite) TestUndelegationCompletion() {
	s.SetupCCVChannel(s.path)

	// delegate bondAmt and undelegate 1/4 of it
	bondAmt := sdk.NewInt(10000000)
	delAddr := s.providerChain.SenderAccount.GetAddress()
	initBalance, valsetUpdateID := delegateAndUndelegate(s, delAddr, bondAmt, 4)
	// - check that staking unbonding op was created
	checkStakingUnbondingOps(s, 1, true)

	// call NextBlock on the provider (which increments the height)
	s.providerChain.NextBlock()

	// unbond on provider
	stakingKeeper := s.providerApp.GetTestStakingKeeper()
	incrementTime(s, stakingKeeper.UnbondingTime(s.providerCtx()))

	// check that the unbonding operation completed
	checkStakingUnbondingOps(s, valsetUpdateID, false)
	// - check that necessary delegated coins have been returned
	unbondAmt := bondAmt.Quo(sdk.NewInt(4))
	stillBondedAmt := bondAmt.Sub(unbondAmt)
	s.Require().Equal(
		initBalance.Sub(stillBondedAmt),
		getBalance(s, s.providerCtx(), delAddr),
		"unexpected initial balance after unbonding; test: %s",
	)
}
