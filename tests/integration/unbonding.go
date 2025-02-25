package integration

import (
	"cosmossdk.io/math"

	sdk "github.com/cosmos/cosmos-sdk/types"
)

// TestUndelegationCompletion tests that undelegations complete after
// the unbonding period elapses on the provider, regardless of the consumer's state
// @Long Description@
// * Set up CCV channel.
// * Perform initial delegation of tokens followed by a partial undelegation (1/4 of the tokens).
// * Verify that the staking unbonding operation is created as expected.
// * Increment provider block height.
// * Check that the unbonding operation has been completed.
// * Verify that the token balances are correctly updated and the expected amount of tokens has been returned to the account.
func (s *CCVTestSuite) TestUndelegationCompletion() {
	s.SetupCCVChannel(s.path)

	// delegate bondAmt and undelegate 1/4 of it
	bondAmt := math.NewInt(10000000)
	delAddr := s.providerChain.SenderAccount.GetAddress()
	initBalance, valsetUpdateID := delegateAndUndelegate(s, delAddr, bondAmt, 4)
	// - check that staking unbonding op was created
	checkStakingUnbondingOps(s, 1, true)

	// call NextBlock on the provider (which increments the height)
	s.providerChain.NextBlock()

	// unbond on provider
	stakingKeeper := s.providerApp.GetTestStakingKeeper()
	unbondingPeriod, err := stakingKeeper.UnbondingTime(s.providerCtx())
	s.Require().NoError(err)
	incrementTime(s, unbondingPeriod)

	// check that the unbonding operation completed
	checkStakingUnbondingOps(s, valsetUpdateID, false)
	// - check that necessary delegated coins have been returned
	unbondAmt := bondAmt.Quo(math.NewInt(4))
	stillBondedAmt := bondAmt.Sub(unbondAmt)
	s.Require().Equal(
		initBalance.Sub(stillBondedAmt),
		getBalance(s, s.providerCtx(), delAddr),
		"unexpected initial balance after unbonding; test: %s",
	)
}

// TestConsumerUnjailNoOp check that consumerKeeper can call .Unjail() without error.
// This operation must only be available in case the app also implements a "standalone" staking keeper.
func (s *CCVTestSuite) TestConsumerUnjailNoOp() {
	consumerKeeper := s.consumerApp.GetConsumerKeeper()

	if s.consumerApp.GetStakingKeeper() == nil {
		// this is a no-op
		err := consumerKeeper.Unjail(s.consumerCtx(), sdk.ConsAddress([]byte{0x01, 0x02, 0x03}))
		s.Require().NoError(err)
	}
}
