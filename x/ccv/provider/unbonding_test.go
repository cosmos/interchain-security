package provider_test

import (
	"strings"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingkeeper "github.com/cosmos/cosmos-sdk/x/staking/keeper"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	"github.com/cosmos/interchain-security/x/ccv/utils"

	ibctesting "github.com/cosmos/ibc-go/v3/testing"

	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	appProvider "github.com/cosmos/interchain-security/app/provider"
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
	relayAllCommittedPackets(s, s.providerChain, s.path, providertypes.PortID, s.path.EndpointB.ChannelID, 1)

	// increment time so that the unbonding period ends on the provider
	incrementTimeByUnbondingPeriod(s, Provider)

	// check that onHold is true
	checkStakingUnbondingOps(s, 1, true, true)
	// check that the unbonding is not complete
	s.Require().True(getBalance(s, s.providerCtx(), delAddr).Equal(initBalance.Sub(bondAmt)))

	// increment time so that the unbonding period ends on the consumer
	incrementTimeByUnbondingPeriod(s, Consumer)

	// relay 1 VSCMatured packet from consumer to provider
	relayAllCommittedPackets(s, s.consumerChain, s.path, consumertypes.PortID, s.path.EndpointA.ChannelID, 1)

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
	relayAllCommittedPackets(s, s.providerChain, s.path, providertypes.PortID, s.path.EndpointB.ChannelID, 1)

	// increment time so that the unbonding period ends on the consumer
	incrementTimeByUnbondingPeriod(s, Consumer)

	// relay 1 VSCMatured packet from consumer to provider
	relayAllCommittedPackets(s, s.consumerChain, s.path, consumertypes.PortID, s.path.EndpointA.ChannelID, 1)

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
	relayAllCommittedPackets(s, s.providerChain, s.path, providertypes.PortID, s.path.EndpointB.ChannelID, 1)

	// check that the unbonding is not complete
	s.Require().True(getBalance(s, s.providerCtx(), delAddr).Equal(initBalance.Sub(bondAmt)))

	// increment time so that the unbonding period ends on the consumer
	incrementTimeByUnbondingPeriod(s, Consumer)

	// relay 1 VSCMatured packet from consumer to provider
	relayAllCommittedPackets(s, s.consumerChain, s.path, consumertypes.PortID, s.path.EndpointA.ChannelID, 1)

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
// 	- no undelegations can complete, even if the provider unbonding period elapses
// 	- all the VSC packets are stored in state as pending
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
	relayAllCommittedPackets(s, s.providerChain, s.path, providertypes.PortID, s.path.EndpointB.ChannelID, 2)

	// increment time so that the unbonding period ends on the consumer
	incrementTimeByUnbondingPeriod(s, Consumer)

	// relay VSCMatured packets from consumer to provider
	relayAllCommittedPackets(s, s.consumerChain, s.path, consumertypes.PortID, s.path.EndpointA.ChannelID, 2)

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
func (s *ProviderTestSuite) TestRedelegationNoConsumer() {
	// remove the consumer chain, which was already registered during setup
	s.providerChain.App.(*appProvider.App).ProviderKeeper.DeleteConsumerClientId(s.providerCtx(), s.consumerChain.ChainID)

	bondAmt := sdk.NewInt(1000000000)
	delAddr := s.providerChain.SenderAccount.GetAddress()
	// Delegate to first validator
	_, shares, validatorAddr := delegate(s, delAddr, bondAmt)

	// TODO: deal with denoms
	s.Require().Equal(shares.Mul(sdk.NewDec(1000000)), bondAmt.ToDec())

	// Pick new validator for redelegation
	_, newValidatorAddr := s.getVal(1)

	// redelegate shares to new validator
	redelegate(s, delAddr, validatorAddr, newValidatorAddr, shares)
}

func getBalance(s *ProviderTestSuite, providerCtx sdk.Context, delAddr sdk.AccAddress) sdk.Int {
	return s.providerChain.App.(*appProvider.App).BankKeeper.GetBalance(providerCtx, delAddr, s.providerBondDenom()).Amount
}

// delegateAndUndelegate delegates bondAmt from delAddr to the first validator
// and then immediately undelegates 1/shareDiv of that delegation
func delegateAndUndelegate(s *ProviderTestSuite, delAddr sdk.AccAddress, bondAmt sdk.Int, shareDiv int64) (initBalance sdk.Int, valsetUpdateId uint64) {
	// delegate
	initBalance, shares, valAddr := delegate(s, delAddr, bondAmt)

	// check that the correct number of tokens were taken out of the delegator's account
	s.Require().True(getBalance(s, s.providerCtx(), delAddr).Equal(initBalance.Sub(bondAmt)))

	// undelegate 1/shareDiv
	valsetUpdateId = undelegate(s, delAddr, valAddr, shares.QuoInt64(shareDiv))

	// check that the tokens have not been returned yet
	s.Require().True(getBalance(s, s.providerCtx(), delAddr).Equal(initBalance.Sub(bondAmt)))

	return initBalance, valsetUpdateId
}

// delegate delegates bondAmt to the first validator
func delegate(s *ProviderTestSuite, delAddr sdk.AccAddress, bondAmt sdk.Int) (initBalance sdk.Int, shares sdk.Dec, valAddr sdk.ValAddress) {
	initBalance = getBalance(s, s.providerCtx(), delAddr)
	// choose a validator
	validator, valAddr := s.getVal(0)
	// delegate bondAmt tokens on provider to change validator powers
	shares, err := s.providerChain.App.(*appProvider.App).StakingKeeper.Delegate(
		s.providerCtx(),
		delAddr,
		bondAmt,
		stakingtypes.Unbonded,
		stakingtypes.Validator(validator),
		true,
	)
	s.Require().NoError(err)
	// check that the correct number of tokens were taken out of the delegator's account
	s.Require().True(getBalance(s, s.providerCtx(), delAddr).Equal(initBalance.Sub(bondAmt)))
	return initBalance, shares, valAddr
}

// undelegate unbonds an amount of delegator shares from a given validator
func undelegate(s *ProviderTestSuite, delAddr sdk.AccAddress, valAddr sdk.ValAddress, sharesAmount sdk.Dec) (valsetUpdateId uint64) {
	_, err := s.providerChain.App.(*appProvider.App).StakingKeeper.Undelegate(s.providerCtx(), delAddr, valAddr, sharesAmount)
	s.Require().NoError(err)

	// save the current valset update ID
	valsetUpdateID := s.providerChain.App.(*appProvider.App).ProviderKeeper.GetValidatorSetUpdateId(s.providerCtx())

	return valsetUpdateID
}

func redelegate(s *ProviderTestSuite, delAddr sdk.AccAddress, valSrcAddr sdk.ValAddress,
	ValDstAddr sdk.ValAddress, sharesAmount sdk.Dec) {
	// delegate bondAmt tokens on provider to change validator powers
	completionTime, err := s.providerChain.App.(*appProvider.App).StakingKeeper.BeginRedelegation(
		s.providerCtx(),
		delAddr,
		valSrcAddr,
		ValDstAddr,
		sharesAmount,
	)
	s.Require().NoError(err)
	providerUnbondingPeriod := s.providerChain.App.GetStakingKeeper().UnbondingTime(s.providerCtx())
	s.Require().Equal(s.providerCtx().BlockHeader().Time.Add(providerUnbondingPeriod), completionTime)
}

// ChainType defines the type of chain (either provider or consumer)
type ChainType int

const (
	Provider ChainType = iota
	Consumer
)

// incrementTimeByUnbondingPeriod increments the overall time by
// 	- if provider == true, the unbonding period on the provider;
//	- otherwise, the unbonding period on the consumer.
// Note that it is expected for the provider unbonding period
// to be one day larger than the consumer unbonding period.
func incrementTimeByUnbondingPeriod(s *ProviderTestSuite, chainType ChainType) {
	// Get unboding period from staking keeper
	providerUnbondingPeriod := s.providerChain.App.GetStakingKeeper().UnbondingTime(s.providerCtx())
	consumerUnbondingPeriod, found := s.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetUnbondingTime(s.consumerCtx())
	s.Require().True(found)
	expectedUnbondingPeriod := utils.ComputeConsumerUnbondingPeriod(providerUnbondingPeriod)
	s.Require().Equal(expectedUnbondingPeriod+24*time.Hour, providerUnbondingPeriod, "unexpected provider unbonding period")
	s.Require().Equal(expectedUnbondingPeriod, consumerUnbondingPeriod, "unexpected consumer unbonding period")
	var jumpPeriod time.Duration
	if chainType == Provider {
		jumpPeriod = providerUnbondingPeriod
	} else {
		jumpPeriod = consumerUnbondingPeriod
	}
	// Make sure the clients do not expire
	jumpPeriod = jumpPeriod/4 + time.Hour
	for i := 0; i < 4; i++ {
		s.coordinator.IncrementTimeBy(jumpPeriod)
		// Update the provider client on the consumer
		err := s.path.EndpointA.UpdateClient()
		s.Require().NoError(err)
		// Update the consumer client on the provider
		err = s.path.EndpointB.UpdateClient()
		s.Require().NoError(err)
	}
}

// relayAllCommittedPackets relays all committed packets from `srcChain` on `path`
func relayAllCommittedPackets(
	s *ProviderTestSuite,
	srcChain *ibctesting.TestChain,
	path *ibctesting.Path,
	portID string,
	channelID string,
	expectedPackets int,
) {
	// check that the packets are committed in  state
	commitments := srcChain.App.GetIBCKeeper().ChannelKeeper.GetAllPacketCommitmentsAtChannel(
		srcChain.GetContext(),
		portID,
		channelID,
	)
	s.Require().Equal(expectedPackets, len(commitments), "did not find packet commitments")

	// relay all packets from srcChain to counterparty
	for _, commitment := range commitments {
		// - get packets
		packet, found := srcChain.GetSentPacket(commitment.Sequence)
		s.Require().True(found, "did not find sent packet")
		// - relay the packet
		err := path.RelayPacket(packet)
		s.Require().NoError(err)
	}
}

func checkStakingUnbondingOps(s *ProviderTestSuite, id uint64, found bool, onHold bool) {
	stakingUnbondingOp, wasFound := getStakingUnbondingDelegationEntry(s.providerCtx(), s.providerChain.App.(*appProvider.App).StakingKeeper, id)
	s.Require().True(found == wasFound)
	s.Require().True(onHold == stakingUnbondingOp.UnbondingOnHold)
}

func checkCCVUnbondingOp(s *ProviderTestSuite, providerCtx sdk.Context, chainID string, valUpdateID uint64, found bool) {
	entries, wasFound := s.providerChain.App.(*appProvider.App).ProviderKeeper.GetUnbondingOpsFromIndex(providerCtx, chainID, valUpdateID)
	s.Require().True(found == wasFound)
	if found {
		s.Require().True(len(entries) > 0, "No unbonding ops found")
		s.Require().True(len(entries[0].UnbondingConsumerChains) > 0, "Unbonding op with no consumer chains")
		s.Require().True(strings.Compare(entries[0].UnbondingConsumerChains[0], "testchain2") == 0, "Unbonding op with unexpected consumer chain")
	}
}

func getStakingUnbondingDelegationEntry(ctx sdk.Context, k stakingkeeper.Keeper, id uint64) (stakingUnbondingOp stakingtypes.UnbondingDelegationEntry, found bool) {
	stakingUbd, found := k.GetUnbondingDelegationByUnbondingId(ctx, id)

	for _, entry := range stakingUbd.Entries {
		if entry.UnbondingId == id {
			stakingUnbondingOp = entry
			found = true
			break
		}
	}

	return stakingUnbondingOp, found
}
