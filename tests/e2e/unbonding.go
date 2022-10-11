package e2e

import (
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"

	appProvider "github.com/cosmos/interchain-security/app/provider"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
)

// TestUndelegationProviderFirst checks that an unbonding operation completes
// when the unbonding period elapses first on the provider chain
func (s *CCVTestSuite) TestUndelegationProviderFirst() {
	s.SetupCCVChannel()
	s.SetupTransferChannel()

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
func (s *CCVTestSuite) TestUndelegationConsumerFirst() {
	s.SetupCCVChannel()
	s.SetupTransferChannel()

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
func (s *CCVTestSuite) TestUndelegationNoValsetChange() {
	s.SetupCCVChannel()
	s.SetupTransferChannel()

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
func (s *CCVTestSuite) TestUndelegationDuringInit() {
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
	s.SetupTransferChannel()

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
func (s *CCVTestSuite) TestUnbondingNoConsumer() {
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
	// cannot use incrementTimeByUnbondingPeriod() since it tries
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

// TestRedelegationNoConsumer tests a redelegate transaction
// submitted on a provider chain with no consumers
func (s *CCVTestSuite) TestRedelegationNoConsumer() {

	providerKeeper := s.providerChain.App.(*appProvider.App).ProviderKeeper
	stakingKeeper := s.providerChain.App.(*appProvider.App).StakingKeeper

	// remove the consumer chain, which was already registered during setup
	providerKeeper.DeleteConsumerClientId(s.providerCtx(), s.consumerChain.ChainID)

	// Setup delegator, bond amount, and src/dst validators
	bondAmt := sdk.NewInt(10000000)
	delAddr := s.providerChain.SenderAccount.GetAddress()
	_, srcVal := s.getVal(0)
	_, dstVal := s.getVal(1)

	delegateAndRedelegate(
		s,
		delAddr,
		srcVal,
		dstVal,
		bondAmt,
	)

	// 1 redelegation record should exist for original delegator
	redelegations := checkRedelegations(s, delAddr, 1)

	// Check that the only entry has appropriate maturation time, the unbonding period from now
	checkRedelegationEntryCompletionTime(
		s,
		redelegations[0].Entries[0],
		s.providerCtx().BlockTime().Add(stakingKeeper.UnbondingTime(s.providerCtx())),
	)

	// Increment time so that the unbonding period passes on the provider
	incrementTimeByUnbondingPeriod(s, Provider)

	// Call NextBlock on the provider (which increments the height)
	s.providerChain.NextBlock()

	// No redelegation records should exist for original delegator anymore
	checkRedelegations(s, delAddr, 0)
}

// TestRedelegationWithConsumer tests a redelegate transaction submitted on a provider chain
// when the unbonding period elapses first on the provider chain
func (s *CCVTestSuite) TestRedelegationProviderFirst() {
	s.SetupCCVChannel()
	s.SetupTransferChannel()

	stakingKeeper := s.providerChain.App.(*appProvider.App).StakingKeeper
	providerKeeper := s.providerChain.App.(*appProvider.App).ProviderKeeper

	// Setup delegator, bond amount, and src/dst validators
	bondAmt := sdk.NewInt(10000000)
	delAddr := s.providerChain.SenderAccount.GetAddress()
	_, srcVal := s.getVal(0)
	_, dstVal := s.getVal(1)

	delegateAndRedelegate(
		s,
		delAddr,
		srcVal,
		dstVal,
		bondAmt,
	)

	// 1 redelegation record should exist for original delegator
	redelegations := checkRedelegations(s, delAddr, 1)

	// Check that the only entry has appropriate maturation time, the unbonding period from now
	checkRedelegationEntryCompletionTime(
		s,
		redelegations[0].Entries[0],
		s.providerCtx().BlockTime().Add(stakingKeeper.UnbondingTime(s.providerCtx())),
	)

	// Save the current valset update ID
	valsetUpdateID := providerKeeper.GetValidatorSetUpdateId(s.providerCtx())

	// Check that CCV unbonding op was created from AfterUnbondingInitiated hook
	checkCCVUnbondingOp(s, s.providerCtx(), s.consumerChain.ChainID, valsetUpdateID, true)

	// Call NextBlock on the provider (which increments the height)
	s.providerChain.NextBlock()

	// Relay 2 VSC packets from provider to consumer (original delegation, and redelegation)
	relayAllCommittedPackets(s, s.providerChain, s.path,
		ccv.ProviderPortID, s.path.EndpointB.ChannelID, 2)

	// Increment time so that the unbonding period ends on the provider
	incrementTimeByUnbondingPeriod(s, Provider)

	// 1 redelegation record should still exist for original delegator on provider
	checkRedelegations(s, delAddr, 1)

	// CCV unbonding op should also still exist
	checkCCVUnbondingOp(s, s.providerCtx(), s.consumerChain.ChainID, valsetUpdateID, true)

	// Increment time so that the unbonding period ends on the consumer
	incrementTimeByUnbondingPeriod(s, Consumer)

	// Relay 2 VSCMatured packets from consumer to provider (original delegation and redelegation)
	relayAllCommittedPackets(s, s.consumerChain,
		s.path, ccv.ConsumerPortID, s.path.EndpointA.ChannelID, 2)

	//
	// Check that the redelegation operation has now completed on provider
	//

	// Redelegation record should be deleted for original delegator
	checkRedelegations(s, delAddr, 0)

	// Check that ccv unbonding op has been deleted
	checkCCVUnbondingOp(s, s.providerCtx(), s.consumerChain.ChainID, valsetUpdateID, false)
}
