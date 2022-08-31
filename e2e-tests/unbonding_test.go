package e2e_test

import (
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"

	appProvider "github.com/cosmos/interchain-security/app/provider"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
)

// TestUndelegationProviderFirst checks that an unbonding operation completes
// when the unbonding period elapses first on the provider chain
func (s *ProviderTestSuite) TestUndelegationProviderFirst() {
	s.SetupCCVChannel()

	// delegate bondAmt and undelegate 1/2 of it
	bondAmt := sdk.NewInt(10000000)
	delAddr := s.providerChain.SenderAccount.GetAddress()
	initBalance, valsetUpdateID := delegateAndUndelegate(s, delAddr, bondAmt, 2)
	// - check that staking unbonding op was created and onHold is true
	checkStakingUnbondingOps(s, 1, true, true)
	// - check that CCV unbonding op was created
	checkCCVUnbondingOp(s, s.providerCtx(), s.consumerChain.ChainID, valsetUpdateID, true)

	// call NextBlock on the provider (which increments the height)
	s.providerChain.NextBlock()

	// relay 1 VSC packet from provider to consumer
	relayAllCommittedPackets(s, s.providerChain, s.path, ccv.ProviderPortID, s.path.EndpointB.ChannelID, 1)

	// increment time so that the unbonding period ends on the provider
	incrementTimeByUnbondingPeriod(s, Provider)

	// check that onHold is true
	checkStakingUnbondingOps(s, 1, true, true)
	// check that the unbonding is not complete
	s.Require().True(getBalance(s, s.providerCtx(), delAddr).Equal(initBalance.Sub(bondAmt)))

	// increment time so that the unbonding period ends on the consumer
	incrementTimeByUnbondingPeriod(s, Consumer)

	// relay 1 VSCMatured packet from consumer to provider
	relayAllCommittedPackets(s, s.consumerChain, s.path, ccv.ConsumerPortID, s.path.EndpointA.ChannelID, 1)

	// check that the unbonding operation completed
	// - check that ccv unbonding op has been deleted
	checkCCVUnbondingOp(s, s.providerCtx(), s.consumerChain.ChainID, valsetUpdateID, false)
	// - check that staking unbonding op has been deleted
	checkStakingUnbondingOps(s, valsetUpdateID, false, false)
	// - check that half the delegated coins have been returned
	s.Require().True(getBalance(s, s.providerCtx(), delAddr).Equal(initBalance.Sub(bondAmt.Quo(sdk.NewInt(2)))))
}

// TestUndelegationConsumerFirst checks that an unbonding operation completes
// when the unbonding period elapses first on the consumer chain
func (s *ProviderTestSuite) TestUndelegationConsumerFirst() {
	s.SetupCCVChannel()

	// delegate bondAmt and undelegate 1/2 of it
	bondAmt := sdk.NewInt(10000000)
	delAddr := s.providerChain.SenderAccount.GetAddress()
	initBalance, valsetUpdateID := delegateAndUndelegate(s, delAddr, bondAmt, 2)
	// - check that staking unbonding op was created and onHold is true
	checkStakingUnbondingOps(s, 1, true, true)
	// - check that CCV unbonding op was created
	checkCCVUnbondingOp(s, s.providerCtx(), s.consumerChain.ChainID, valsetUpdateID, true)

	// call NextBlock on the provider (which increments the height)
	s.providerChain.NextBlock()

	// relay 1 VSC packet from provider to consumer
	relayAllCommittedPackets(s, s.providerChain, s.path, ccv.ProviderPortID, s.path.EndpointB.ChannelID, 1)

	// increment time so that the unbonding period ends on the consumer
	incrementTimeByUnbondingPeriod(s, Consumer)

	// relay 1 VSCMatured packet from consumer to provider
	relayAllCommittedPackets(s, s.consumerChain, s.path, ccv.ConsumerPortID, s.path.EndpointA.ChannelID, 1)

	// check that the unbonding is not complete
	s.Require().True(getBalance(s, s.providerCtx(), delAddr).Equal(initBalance.Sub(bondAmt)))

	// increment time so that the unbonding period ends on the provider
	incrementTimeByUnbondingPeriod(s, Provider)

	// check that the unbonding operation completed
	// - check that ccv unbonding op has been deleted
	checkCCVUnbondingOp(s, s.providerCtx(), s.consumerChain.ChainID, valsetUpdateID, false)
	// - check that staking unbonding op has been deleted
	checkStakingUnbondingOps(s, valsetUpdateID, false, false)
	// - check that half the delegated coins have been returned
	s.Require().True(getBalance(s, s.providerCtx(), delAddr).Equal(initBalance.Sub(bondAmt.Quo(sdk.NewInt(2)))))
}

// TestUndelegationNoValsetChange checks that an unbonding operation completes
// even when the validator set is not changed
func (s *ProviderTestSuite) TestUndelegationNoValsetChange() {
	s.SetupCCVChannel()

	// delegate bondAmt and undelegate all of it
	bondAmt := sdk.NewInt(10000000)
	delAddr := s.providerChain.SenderAccount.GetAddress()
	initBalance, valsetUpdateID := delegateAndUndelegate(s, delAddr, bondAmt, 1)
	// - check that staking unbonding op was created and onHold is true
	checkStakingUnbondingOps(s, 1, true, true)
	// - check that CCV unbonding op was created
	checkCCVUnbondingOp(s, s.providerCtx(), s.consumerChain.ChainID, valsetUpdateID, true)

	// call NextBlock on the provider (which increments the height)
	s.providerChain.NextBlock()

	// relay 1 VSC packet from provider to consumer
	relayAllCommittedPackets(s, s.providerChain, s.path, ccv.ProviderPortID, s.path.EndpointB.ChannelID, 1)

	// check that the unbonding is not complete
	s.Require().True(getBalance(s, s.providerCtx(), delAddr).Equal(initBalance.Sub(bondAmt)))

	// increment time so that the unbonding period ends on the consumer
	incrementTimeByUnbondingPeriod(s, Consumer)

	// relay 1 VSCMatured packet from consumer to provider
	relayAllCommittedPackets(s, s.consumerChain, s.path, ccv.ConsumerPortID, s.path.EndpointA.ChannelID, 1)

	// increment time so that the unbonding period ends on the provider
	incrementTimeByUnbondingPeriod(s, Provider)

	// check that the unbonding operation completed
	// - check that ccv unbonding op has been deleted
	checkCCVUnbondingOp(s, s.providerCtx(), s.consumerChain.ChainID, valsetUpdateID, false)
	// - check that staking unbonding op has been deleted
	checkStakingUnbondingOps(s, valsetUpdateID, false, false)
	// - check that all the delegated coins have been returned
	s.Require().True(getBalance(s, s.providerCtx(), delAddr).Equal(initBalance))
}

// TestUndelegationDuringInit checks that before the CCV channel is established
//   - no undelegations can complete, even if the provider unbonding period elapses
//   - all the VSC packets are stored in state as pending
func (s *ProviderTestSuite) TestUndelegationDuringInit() {
	// delegate bondAmt and undelegate 1/2 of it
	bondAmt := sdk.NewInt(10000000)
	delAddr := s.providerChain.SenderAccount.GetAddress()
	initBalance, valsetUpdateID := delegateAndUndelegate(s, delAddr, bondAmt, 2)
	// - check that staking unbonding op was created and onHold is true
	checkStakingUnbondingOps(s, 1, true, true)
	// - check that CCV unbonding op was created
	checkCCVUnbondingOp(s, s.providerCtx(), s.consumerChain.ChainID, valsetUpdateID, true)

	// call NextBlock on the provider (which increments the height)
	s.providerChain.NextBlock()

	// check that the VSC packet is stored in state as pending
	pendingVSCs, _ := s.providerChain.App.(*appProvider.App).ProviderKeeper.GetPendingVSCs(s.providerCtx(), s.consumerChain.ChainID)
	s.Require().True(len(pendingVSCs) == 1, "no pending VSC packet found")

	// delegate again to create another VSC packet
	delegate(s, delAddr, bondAmt)

	// call NextBlock on the provider (which increments the height)
	s.providerChain.NextBlock()

	// check that the VSC packet is stored in state as pending
	pendingVSCs, _ = s.providerChain.App.(*appProvider.App).ProviderKeeper.GetPendingVSCs(s.providerCtx(), s.consumerChain.ChainID)
	s.Require().True(len(pendingVSCs) == 2, "only one pending VSC packet found")

	// increment time so that the unbonding period ends on the provider
	incrementTimeByUnbondingPeriod(s, Provider)
	// - check that the unbonding op is still there and onHold is true
	checkStakingUnbondingOps(s, 1, true, true)
	// - check that unbonding has not yet completed, i.e., the initBalance
	// is still lower by the bond amount, because it has been taken out of
	// the delegator's account
	s.Require().True(getBalance(s, s.providerCtx(), delAddr).Equal(initBalance.Sub(bondAmt).Sub(bondAmt)))

	// complete CCV channel setup
	s.SetupCCVChannel()

	// relay VSC packets from provider to consumer
	relayAllCommittedPackets(s, s.providerChain, s.path, ccv.ProviderPortID, s.path.EndpointB.ChannelID, 2)

	// increment time so that the unbonding period ends on the consumer
	incrementTimeByUnbondingPeriod(s, Consumer)

	// relay VSCMatured packets from consumer to provider
	relayAllCommittedPackets(s, s.consumerChain, s.path, ccv.ConsumerPortID, s.path.EndpointA.ChannelID, 2)

	// check that the unbonding operation completed
	// - check that ccv unbonding op has been deleted
	checkCCVUnbondingOp(s, s.providerCtx(), s.consumerChain.ChainID, valsetUpdateID, false)
	// - check that staking unbonding op has been deleted
	checkStakingUnbondingOps(s, valsetUpdateID, false, false)
	// - check that one quarter the delegated coins have been returned
	s.Require().True(getBalance(s, s.providerCtx(), delAddr).Equal(initBalance.Sub(bondAmt).Sub(bondAmt.Quo(sdk.NewInt(2)))))
}

// TODO FIX, the consumer is added during SetupTest()
// Bond some tokens on provider
// Unbond them to create unbonding op
// Check unbonding ops on both sides
// Advance time so that provider's unbonding op completes
// Check that unbonding has completed in provider staking
func (s *ProviderTestSuite) TestUnbondingNoConsumer() {
	// remove the consumer chain, which was already registered during setup
	s.providerChain.App.(*appProvider.App).ProviderKeeper.DeleteConsumerClientId(s.providerCtx(), s.consumerChain.ChainID)

	// delegate bondAmt and undelegate 1/2 of it
	bondAmt := sdk.NewInt(10000000)
	delAddr := s.providerChain.SenderAccount.GetAddress()
	initBalance, valsetUpdateID := delegateAndUndelegate(s, delAddr, bondAmt, 2)
	// - check that staking unbonding op was created and onHold is FALSE
	checkStakingUnbondingOps(s, 1, true, false)
	// - check that CCV unbonding op was NOT created
	checkCCVUnbondingOp(s, s.providerCtx(), s.consumerChain.ChainID, valsetUpdateID, false)

	// increment time so that the unbonding period ends on the provider;
	// cannot use incrementTimeByProviderUnbondingPeriod() since it tries
	// to also update the provider's client on the consumer
	providerUnbondingPeriod := s.providerChain.App.GetStakingKeeper().UnbondingTime(s.providerCtx())
	s.coordinator.IncrementTimeBy(providerUnbondingPeriod + time.Hour)

	// call NextBlock on the provider (which increments the height)
	s.providerChain.NextBlock()

	// check that the unbonding operation completed
	// - check that staking unbonding op has been deleted
	checkStakingUnbondingOps(s, valsetUpdateID, false, false)
	// - check that half the coins have been returned
	s.Require().True(getBalance(s, s.providerCtx(), delAddr).Equal(initBalance.Sub(bondAmt.Quo(sdk.NewInt(2)))))
}

// TestRedelegationNoConsumer tests a redelegate transaction submitted on a provider chain with no consumers
func (s *ProviderTestSuite) TestRedelegationNoConsumer() {
	providerKeeper := s.providerChain.App.(*appProvider.App).ProviderKeeper
	stakingKeeper := s.providerChain.App.(*appProvider.App).StakingKeeper

	// remove the consumer chain, which was already registered during setup
	providerKeeper.DeleteConsumerClientId(s.providerCtx(), s.consumerChain.ChainID)

	// Setup delegator and bond amount
	bondAmt := sdk.NewInt(10000000)
	delAddr := s.providerChain.SenderAccount.GetAddress()

	// Delegate to validator 0
	_, val0Addr := s.getVal(0)
	val0TokensBefore := stakingKeeper.Validator(s.providerCtx(), val0Addr).GetBondedTokens()
	val0PowerBefore := stakingKeeper.GetLastValidatorPower(s.providerCtx(), val0Addr)
	_, shares, _ := delegate(s, delAddr, bondAmt)

	// Assert expected amount was bonded to validator 0
	val0TokensAfter := stakingKeeper.Validator(s.providerCtx(), val0Addr).GetBondedTokens()
	s.Require().Equal(val0TokensAfter.Sub(val0TokensBefore), bondAmt)

	s.providerChain.NextBlock()

	// Check validator power
	val0PowerAfter := stakingKeeper.GetLastValidatorPower(s.providerCtx(), val0Addr)
	s.Require().Greater(val0PowerAfter, val0PowerBefore)

	// Pick new validator for redelegation
	_, val1Addr := s.getVal(1)
	val1TokensBefore := stakingKeeper.Validator(s.providerCtx(), val1Addr).GetBondedTokens()
	val1PowerBefore := stakingKeeper.GetLastValidatorPower(s.providerCtx(), val1Addr)

	// redelegate shares to new validator
	redelegate(s, delAddr,
		val0Addr, // Source
		val1Addr, // Dest
		shares)

	// Assert expected amount was delegated to validator 1
	val1TokensAfter := stakingKeeper.Validator(s.providerCtx(), val1Addr).GetBondedTokens()
	s.Require().Equal(val1TokensAfter.Sub(val1TokensBefore), bondAmt)

	// Assert delegated tokens amount returned to original value for validator 0
	s.Require().Equal(val0TokensBefore, stakingKeeper.Validator(s.providerCtx(), val0Addr).GetBondedTokens())

	s.providerChain.NextBlock()

	// 1 redelegation record should exist with appropriate maturation time
	redelegations := stakingKeeper.GetRedelegations(s.providerCtx(), delAddr, 2)
	s.Require().Len(redelegations, 1)
	redelgation := redelegations[0]
	providerUnbondingPeriod := stakingKeeper.UnbondingTime(s.providerCtx())
	s.Require().Equal(
		s.providerCtx().BlockTime().Add(providerUnbondingPeriod),
		redelgation.Entries[0].CompletionTime)

	// Check validator powers
	val1PowerAfter := stakingKeeper.GetLastValidatorPower(s.providerCtx(), val1Addr)
	s.Require().Greater(val1PowerAfter, val1PowerBefore)
	s.Require().Equal(val0PowerBefore, stakingKeeper.GetLastValidatorPower(s.providerCtx(), val0Addr))
}

// TestRedelegationWithConsumer tests a redelegate transaction submitted on a provider chain with a consumer
func (s *ProviderTestSuite) TestRedelegationWithConsumer() {
	// TODO
}
