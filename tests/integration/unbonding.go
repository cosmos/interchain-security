package integration

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
)

// TestUndelegationCompletion tests that undelegations complete after
// the unbonding period elapses on the provider, regardless of the consumer's state
func (s *CCVTestSuite) TestUndelegationCompletion() {
	s.SetupCCVChannel(s.path)

	// delegate bondAmt and undelegate 1/2 of it
	bondAmt := sdk.NewInt(10000000)
	delAddr := s.providerChain.SenderAccount.GetAddress()
	initBalance, valsetUpdateID := delegateAndUndelegate(s, delAddr, bondAmt, 2)
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
	unbondAmt := bondAmt.Sub(bondAmt.Quo(sdk.NewInt(2)))
	s.Require().Equal(
		initBalance.Sub(unbondAmt),
		getBalance(s, s.providerCtx(), delAddr),
		"unexpected initial balance after unbonding; test: %s",
	)
}

// This test reproduces a fixed bug when an inactive validator enters back into the active set.
// It used to cause a panic in the provider module hook called by AfterUnbondingInitiated
// during the staking module EndBlock.
func (s *CCVTestSuite) TestTooManyLastValidators() {
	sk := s.providerApp.GetTestStakingKeeper()
	pk := s.providerApp.GetProviderKeeper()

	// get current staking params
	p := sk.GetParams(s.providerCtx())

	// get validators, which are all active at the moment
	vals := sk.GetAllValidators(s.providerCtx())
	s.Require().Equal(len(vals), len(pk.GetLastBondedValidators(s.providerCtx())))

	// jail a validator
	val := vals[0]
	consAddr, err := val.GetConsAddr()
	s.Require().NoError(err)
	sk.Jail(s.providerCtx(), consAddr)

	// save the current number of bonded vals
	lastVals := pk.GetLastBondedValidators(s.providerCtx())

	// pass one block to apply the validator set changes
	// (calls ApplyAndReturnValidatorSetUpdates in the the staking module EndBlock)
	s.providerChain.NextBlock()

	// verify that the number of bonded validators is decreased by one
	s.Require().Equal(len(lastVals)-1, len(pk.GetLastBondedValidators(s.providerCtx())))

	// update maximum validator to equal the number of bonded validators
	p.MaxValidators = uint32(len(pk.GetLastBondedValidators(s.providerCtx())))
	sk.SetParams(s.providerCtx(), p)

	// pass one block to apply validator set changes
	s.providerChain.NextBlock()

	// unjail validator
	// Note that since validators are sorted in descending order, the unjailed validator
	// enters the active set again since it's ranked first by voting power.
	sk.Unjail(s.providerCtx(), consAddr)

	// pass another block to update the validator set
	// which causes a panic due to a GetLastValidator call in
	// ApplyAndReturnValidatorSetUpdates where the staking module has a inconsistent state
	s.Require().NotPanics(s.providerChain.NextBlock)
	s.Require().NotPanics(func() { sk.ApplyAndReturnValidatorSetUpdates(s.providerCtx()) })
	s.Require().NotPanics(func() { pk.GetLastBondedValidators(s.providerCtx()) })
}
