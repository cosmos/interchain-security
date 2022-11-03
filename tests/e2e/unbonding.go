package e2e

import (
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"

	providerkeeper "github.com/cosmos/interchain-security/x/ccv/provider/keeper"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
)

// TestUndelegationNormalOperation tests that undelegations complete after 
// the unbonding period elapses on both the consumer and provider, without 
// VSC packets timing out.
func (s *CCVTestSuite) TestUndelegationNormalOperation() {
	unbondConsumer := func(expectedPackets int) {
		// relay 1 VSC packet from provider to consumer
		relayAllCommittedPackets(s, s.providerChain, s.path, ccv.ProviderPortID, s.path.EndpointB.ChannelID, expectedPackets)
		// increment time so that the unbonding period ends on the consumer
		incrementTimeByUnbondingPeriod(s, Consumer)
		// relay 1 VSCMatured packet from consumer to provider
		relayAllCommittedPackets(s, s.consumerChain, s.path, ccv.ConsumerPortID, s.path.EndpointA.ChannelID, expectedPackets)
	}

	testCases := []struct {
		name     string
		shareDiv int64
		unbond   func(expBalance, balance sdk.Int)
	}{
		{
			"provider unbonding period elapses first", 2, func(expBalance, balance sdk.Int) {
				// increment time so that the unbonding period ends on the provider
				incrementTimeByUnbondingPeriod(s, Provider)

				// check that onHold is true
				checkStakingUnbondingOps(s, 1, true, true, "unbonding should be on hold")

				// check that the unbonding is not complete
				s.Require().Equal(expBalance, balance, "unexpected balance after provider unbonding")

				// undelegation complete on consumer
				unbondConsumer(1)
			},
		},
		{
			"consumer unbonding period elapses first", 2, func(expBalance, balance sdk.Int) {
				// undelegation complete on consumer
				unbondConsumer(1)

				// check that onHold is false
				checkStakingUnbondingOps(s, 1, true, false, "unbonding should be not be on hold")

				// check that the unbonding is not complete
				s.Require().Equal(expBalance, balance, "unexpected balance after consumer unbonding")

				// increment time so that the unbonding period ends on the provider
				incrementTimeByUnbondingPeriod(s, Provider)
			},
		},
		{
			"no valset changes", 1, func(expBalance, balance sdk.Int) {
				// undelegation complete on consumer
				unbondConsumer(1)

				// check that onHold is false
				checkStakingUnbondingOps(s, 1, true, false, "unbonding should be not be on hold")

				// check that the unbonding is not complete
				s.Require().Equal(expBalance, balance, "unexpected balance after consumer unbonding")

				// increment time so that the unbonding period ends on the provider
				incrementTimeByUnbondingPeriod(s, Provider)
			},
		},
	}

	for i, tc := range testCases {
		providerKeeper := s.providerApp.GetProviderKeeper()
		consumerKeeper := s.consumerApp.GetConsumerKeeper()
		stakingKeeper := s.providerApp.GetE2eStakingKeeper()

		s.SetupCCVChannel()

		// set VSC timeout period to not trigger the removal of the consumer chain
		providerUnbondingPeriod := stakingKeeper.UnbondingTime(s.providerCtx())
		consumerUnbondingPeriod := consumerKeeper.GetUnbondingPeriod(s.consumerCtx())
		providerKeeper.SetVscTimeoutPeriod(s.providerCtx(), providerUnbondingPeriod+consumerUnbondingPeriod+24*time.Hour)

		// delegate bondAmt and undelegate tc.shareDiv of it
		bondAmt := sdk.NewInt(10000000)
		delAddr := s.providerChain.SenderAccount.GetAddress()
		initBalance, valsetUpdateID := delegateAndUndelegate(s, delAddr, bondAmt, tc.shareDiv)
		// - check that staking unbonding op was created and onHold is true
		checkStakingUnbondingOps(s, 1, true, true, "test: "+tc.name)
		// - check that CCV unbonding op was created
		checkCCVUnbondingOp(s, s.providerCtx(), s.consumerChain.ChainID, valsetUpdateID, true, "test: "+tc.name)

		// call NextBlock on the provider (which increments the height)
		s.providerChain.NextBlock()

		// unbond both on provider and consumer and check that
		// the balance remains unchanged in between
		tc.unbond(initBalance.Sub(bondAmt), getBalance(s, s.providerCtx(), delAddr))

		// check that the unbonding operation completed
		// - check that ccv unbonding op has been deleted
		checkCCVUnbondingOp(s, s.providerCtx(), s.consumerChain.ChainID, valsetUpdateID, false, "test: "+tc.name)
		// - check that staking unbonding op has been deleted
		checkStakingUnbondingOps(s, valsetUpdateID, false, false, "test: "+tc.name)
		// - check that necessary delegated coins have been returned
		unbondAmt := bondAmt.Sub(bondAmt.Quo(sdk.NewInt(tc.shareDiv)))
		s.Require().Equal(
			initBalance.Sub(unbondAmt),
			getBalance(s, s.providerCtx(), delAddr),
			"unexpected initial balance after unbonding; test: %s", tc.name,
		)

		if i+1 < len(testCases) {
			// reset suite to reset provider client
			s.SetupTest()
		}
	}
}

// TestUndelegationVscTimeout tests that an undelegation
// completes after vscTimeoutPeriod even if it does not
// reach maturity on the consumer chain. In this case,
// the consumer chain is removed.
func (s *CCVTestSuite) TestUndelegationVscTimeout() {
	providerKeeper := s.providerApp.GetProviderKeeper()

	s.SetupCCVChannel()

	// set VSC timeout period to trigger the removal of the consumer chain
	vscTimeout := providerKeeper.GetVscTimeoutPeriod(s.providerCtx())

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

	// increment time so that the unbonding period ends on the provider
	incrementTimeByUnbondingPeriod(s, Provider)

	// check that onHold is true
	checkStakingUnbondingOps(s, 1, true, true, "unbonding should be on hold")

	// check that the unbonding is not complete
	s.Require().Equal(
		initBalance.Sub(bondAmt),
		getBalance(s, s.providerCtx(), delAddr),
		"unexpected balance after provider unbonding")

	// increment time
	incrementTimeBy(s, vscTimeout)

	// check whether the chain was removed
	chainID := s.consumerChain.ChainID
	_, found := providerKeeper.GetConsumerClientId(s.providerCtx(), chainID)
	s.Require().Equal(false, found, "consumer chain was not removed")

	// check if the chain was properly removed
	s.checkConsumerChainIsRemoved(chainID, false, true)

	// check that the unbonding operation completed
	// - check that ccv unbonding op has been deleted
	checkCCVUnbondingOp(s, s.providerCtx(), s.consumerChain.ChainID, valsetUpdateID, false)
	// - check that staking unbonding op has been deleted
	checkStakingUnbondingOps(s, valsetUpdateID, false, false)
	// - check that necessary delegated coins have been returned
	unbondAmt := bondAmt.Sub(bondAmt.Quo(sdk.NewInt(2)))
	s.Require().Equal(
		initBalance.Sub(unbondAmt),
		getBalance(s, s.providerCtx(), delAddr),
		"unexpected initial balance after VSC timeout",
	)
}

// TestUndelegationDuringInit checks that before the CCV channel is established
//   - no undelegations can complete, even if the provider unbonding period elapses
//   - all the VSC packets are stored in state as pending
//   - if the channel handshake times out, then the undelegation completes
func (s *CCVTestSuite) TestUndelegationDuringInit() {
	testCases := []struct {
		name                       string
		updateInitTimeoutTimestamp func(*providerkeeper.Keeper, time.Duration)
		removed                    bool
	}{
		{
			"channel handshake completes after unbonding period", func(pk *providerkeeper.Keeper, pUnbondingPeriod time.Duration) {
				// change the init timeout timestamp for this consumer chain
				// to make sure the chain is not removed before the unbonding period elapses
				ts := s.providerCtx().BlockTime().Add(pUnbondingPeriod + 24*time.Hour)
				pk.SetInitTimeoutTimestamp(s.providerCtx(), s.consumerChain.ChainID, uint64(ts.UnixNano()))
			}, false,
		},
		{
			"channel handshake times out before unbonding period", func(pk *providerkeeper.Keeper, pUnbondingPeriod time.Duration) {
				// change the init timeout timestamp for this consumer chain
				// to make sure the chain is removed before the unbonding period elapses
				ts := s.providerCtx().BlockTime().Add(pUnbondingPeriod - 24*time.Hour)
				pk.SetInitTimeoutTimestamp(s.providerCtx(), s.consumerChain.ChainID, uint64(ts.UnixNano()))
			}, true,
		},
	}

	for i, tc := range testCases {
		providerKeeper := s.providerApp.GetProviderKeeper()
		stakingKeeper := s.providerApp.GetE2eStakingKeeper()

		// delegate bondAmt and undelegate 1/2 of it
		bondAmt := sdk.NewInt(10000000)
		delAddr := s.providerChain.SenderAccount.GetAddress()
		initBalance, valsetUpdateID := delegateAndUndelegate(s, delAddr, bondAmt, 2)
		// - check that staking unbonding op was created and onHold is true
		checkStakingUnbondingOps(s, 1, true, true, "test: "+tc.name)
		// - check that CCV unbonding op was created
		checkCCVUnbondingOp(s, s.providerCtx(), s.consumerChain.ChainID, valsetUpdateID, true, "test: "+tc.name)

		// get provider unbonding period
		providerUnbondingPeriod := stakingKeeper.UnbondingTime(s.providerCtx())
		// update init timeout timestamp
		tc.updateInitTimeoutTimestamp(&providerKeeper, providerUnbondingPeriod)

		// call NextBlock on the provider (which increments the height)
		s.providerChain.NextBlock()

		// check that the VSC packet is stored in state as pending
		pendingVSCs, _ := providerKeeper.GetPendingVSCs(s.providerCtx(), s.consumerChain.ChainID)
		s.Require().True(len(pendingVSCs) == 1, "no pending VSC packet found; test: %s", tc.name)

		// delegate again to create another VSC packet
		delegate(s, delAddr, bondAmt)

		// call NextBlock on the provider (which increments the height)
		s.providerChain.NextBlock()

		// check that the VSC packet is stored in state as pending
		pendingVSCs, _ = providerKeeper.GetPendingVSCs(s.providerCtx(), s.consumerChain.ChainID)
		s.Require().True(len(pendingVSCs) == 2, "only one pending VSC packet found; test: %s", tc.name)

		// increment time so that the unbonding period ends on the provider
		incrementTimeByUnbondingPeriod(s, Provider)

		// check whether the unbonding op is still there and onHold is true
		checkStakingUnbondingOps(s, 1, !tc.removed, true, "test: "+tc.name)

		if !tc.removed {
			// check that unbonding has not yet completed, i.e., the initBalance
			// is still lower by the bond amount, because it has been taken out of
			// the delegator's account
			s.Require().Equal(
				initBalance.Sub(bondAmt).Sub(bondAmt),
				getBalance(s, s.providerCtx(), delAddr),
				"unexpected initial balance before unbonding; test: %s", tc.name,
			)

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
			checkCCVUnbondingOp(s, s.providerCtx(), s.consumerChain.ChainID, valsetUpdateID, false, "test: "+tc.name)
			// - check that staking unbonding op has been deleted
			checkStakingUnbondingOps(s, valsetUpdateID, false, false, "test: "+tc.name)
			// - check that one quarter the delegated coins have been returned
			s.Require().Equal(
				initBalance.Sub(bondAmt).Sub(bondAmt.Quo(sdk.NewInt(2))),
				getBalance(s, s.providerCtx(), delAddr),
				"unexpected initial balance after unbonding; test: %s", tc.name,
			)
		}

		if i+1 < len(testCases) {
			// reset suite to reset provider client
			s.SetupTest()
		}
	}
}

// Bond some tokens on provider
// Unbond them to create unbonding op
// Check unbonding ops on both sides
// Advance time so that provider's unbonding op completes
// Check that unbonding has completed in provider staking
func (s *CCVTestSuite) TestUnbondingNoConsumer() {

	providerKeeper := s.providerApp.GetProviderKeeper()
	providerStakingKeeper := s.providerApp.GetE2eStakingKeeper()

	// remove the consumer chain, which was already registered during setup
	providerKeeper.DeleteConsumerClientId(s.providerCtx(), s.consumerChain.ChainID)

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
	providerUnbondingPeriod := providerStakingKeeper.UnbondingTime(s.providerCtx())
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

	providerKeeper := s.providerApp.GetProviderKeeper()
	stakingKeeper := s.providerApp.GetE2eStakingKeeper()

	// remove the consumer chain, which was already registered during setup
	providerKeeper.DeleteConsumerClientId(s.providerCtx(), s.consumerChain.ChainID)

	// Setup delegator, bond amount, and src/dst validators
	bondAmt := sdk.NewInt(10000000)
	delAddr := s.providerChain.SenderAccount.GetAddress()
	_, srcVal := s.getValByIdx(0)
	_, dstVal := s.getValByIdx(1)

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

	providerKeeper := s.providerApp.GetProviderKeeper()
	consumerKeeper := s.consumerApp.GetConsumerKeeper()
	stakingKeeper := s.providerApp.GetE2eStakingKeeper()

	// set VSC timeout period to not trigger the removal of the consumer chain
	providerUnbondingPeriod := stakingKeeper.UnbondingTime(s.providerCtx())
	consumerUnbondingPeriod := consumerKeeper.GetUnbondingPeriod(s.consumerCtx())
	providerKeeper.SetVscTimeoutPeriod(s.providerCtx(), providerUnbondingPeriod+consumerUnbondingPeriod+24*time.Hour)

	// Setup delegator, bond amount, and src/dst validators
	bondAmt := sdk.NewInt(10000000)
	delAddr := s.providerChain.SenderAccount.GetAddress()
	_, srcVal := s.getValByIdx(0)
	_, dstVal := s.getValByIdx(1)

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
