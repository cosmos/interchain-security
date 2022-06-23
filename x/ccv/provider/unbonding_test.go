package provider_test

import (
	"bytes"
	"fmt"
	"strings"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingkeeper "github.com/cosmos/cosmos-sdk/x/staking/keeper"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"

	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	appProvider "github.com/cosmos/interchain-security/app/provider"
	"github.com/cosmos/interchain-security/x/ccv/types"

	abci "github.com/tendermint/tendermint/abci/types"
)

// PROVIDER FINISHES FIRST
// Bond some tokens on provider
// Unbond them to create unbonding op
// Check unbonding ops on both sides
// Advance time so that provider's unbonding op completes
// Check that unbonding on staking is not allowed to complete
// Relay valset update to consumer
// Advance time so that consumer's unbonding op completes
// Relay ack to provider
// Check that unbonding has finally completed in provider staking
func (s *ProviderTestSuite) TestTimelyUndelegation2() {
	s.SetupCCVChannel()
	bondAmt := sdk.NewInt(10000000)

	delAddr := s.providerChain.SenderAccount.GetAddress()

	origTime := s.providerCtx().BlockTime()

	// delegate bondAmt and undelegate 1/2 of it
	initBalance, valsetUpdateID := bondAndUnbond(s, delAddr, bondAmt, 2)

	// check that staking unbonding op was created and onHold is true
	checkStakingUnbondingOps(s, 1, true, true)

	// check that CCV unbonding op was created
	checkCCVUnbondingOp(s, s.providerCtx(), s.consumerChain.ChainID, valsetUpdateID, true)

	// SEND PACKET
	s.providerChain.App.EndBlock(abci.RequestEndBlock{})

	// Get validator update created in Endblock to use in reconstructing packet
	valUpdates := s.providerChain.App.(*appProvider.App).StakingKeeper.GetValidatorUpdates(s.providerCtx())

	// Get current blocktime
	oldBlockTime := s.providerCtx().BlockTime()

	// commit block on provider chain and update consumer chain's client
	commitProviderBlock(s)
	// Relay packet to consumer chain
	packet, packetData := sendValUpdatePacket(s, valUpdates, valsetUpdateID, oldBlockTime, 1)

	// ACKNOWLEDGE PACKET
	newProviderCtx := endProviderUnbondingPeriod(s, origTime)
	// check that onHold is true
	checkStakingUnbondingOps(s, 1, true, true)

	// Check that unbonding has not yet completed. The initBalance is still lower
	// by the bond amount, because it has been taken out of the delegator's account
	s.Require().True(getBalance(s, newProviderCtx, delAddr).Equal(initBalance.Sub(bondAmt)))

	// end consumer's unbonding period by advancing time and calling UnbondMaturePackets
	endConsumerUnbondingPeriod(s, origTime)

	// commit block on consumer and update provider client
	commitConsumerBlock(s)

	// send acknowledgement to provider
	sendValUpdateAck(s, newProviderCtx, packet, packetData)

	// Check that ccv unbonding op has been deleted
	checkCCVUnbondingOp(s, newProviderCtx, s.consumerChain.ChainID, valsetUpdateID, false)

	// Check that staking unbonding op has been deleted
	checkStakingUnbondingOps(s, valsetUpdateID, false, false)

	// Check that unbonding has completed
	// Check that half the coins have been returned
	s.Require().True(getBalance(s, newProviderCtx, delAddr).Equal(initBalance.Sub(bondAmt.Quo(sdk.NewInt(2)))))
}

// CONSUMER FINISHES FIRST
// Bond some tokens on provider
// Unbond them to create unbonding op
// Check unbonding ops on both sides
// Relay valset update to consumer
// Advance time so that consumer's unbonding op completes
// Relay ack to provider
// Check that unbonding on staking is not allowed to complete
// Advance time so that provider's unbonding op completes
// Check that unbonding has finally completed in provider staking
func (s *ProviderTestSuite) TestTimelyUndelegation1() {
	s.SetupCCVChannel()
	bondAmt := sdk.NewInt(10000000)

	delAddr := s.providerChain.SenderAccount.GetAddress()

	origTime := s.providerCtx().BlockTime()

	// delegate bondAmt and undelegate 1/2 of it
	initBalance, valsetUpdateID := bondAndUnbond(s, delAddr, bondAmt, 2)

	// check that staking unbonding op was created and onHold is true
	checkStakingUnbondingOps(s, 1, true, true)

	// check that CCV unbonding op was created
	checkCCVUnbondingOp(s, s.providerCtx(), s.consumerChain.ChainID, valsetUpdateID, true)

	// SEND PACKET
	s.providerChain.App.EndBlock(abci.RequestEndBlock{})

	// Get validator update created in Endblock to use in reconstructing packet
	valUpdates := s.providerChain.App.(*appProvider.App).StakingKeeper.GetValidatorUpdates(s.providerCtx())

	// Get current blocktime
	oldBlockTime := s.providerCtx().BlockTime()

	// commit block on provider chain and update consumer chain's client
	commitProviderBlock(s)
	// Relay packet to consumer chain
	packet, packetData := sendValUpdatePacket(s, valUpdates, valsetUpdateID, oldBlockTime, 1)

	// END CONSUMER UNBONDING
	// end consumer's unbonding period by advancing time and calling UnbondMaturePackets
	endConsumerUnbondingPeriod(s, origTime)

	// commit block on consumer and update provider client
	commitConsumerBlock(s)

	// send acknowledgement to provider
	sendValUpdateAck(s, s.providerCtx(), packet, packetData)

	// CHECK THAT UNBONDING IS NOT COMPLETE
	// Check that unbonding has not yet completed. The initBalance is still lower
	// by the bond amount, because it has been taken out of the delegator's account
	s.Require().True(getBalance(s, s.providerCtx(), delAddr).Equal(initBalance.Sub(bondAmt)))

	// END PROVIDER UNBONDING
	newProviderCtx := endProviderUnbondingPeriod(s, origTime)

	// CHECK THAT UNBONDING IS COMPLETE
	// Check that ccv unbonding op has been deleted
	checkCCVUnbondingOp(s, newProviderCtx, s.consumerChain.ChainID, valsetUpdateID, false)

	// Check that staking unbonding op has been deleted
	checkStakingUnbondingOps(s, valsetUpdateID, false, false)

	// Check that unbonding has completed
	// Check that half the coins have been returned
	s.Require().True(getBalance(s, newProviderCtx, delAddr).Equal(initBalance.Sub(bondAmt.Quo(sdk.NewInt(2)))))
}

// EDGE CASE
// Bond some tokens on provider
// Unbond all of them to create unbonding op, w/o updating the validator set
// Check unbonding ops on both sides
// Check that a packet commitment was store in state
// Relay valset update to consumer
// Check that unbonding on staking is not allowed to complete
// Advance time so that consumer's unbonding op completes
// Relay ack to provider
// Advance time so that provider's unbonding op completes
// Check that unbonding has finally completed in provider staking
func (s *ProviderTestSuite) TestUndelegationEdgeCase() {
	s.SetupCCVChannel()
	bondAmt := sdk.NewInt(10000000)

	delAddr := s.providerChain.SenderAccount.GetAddress()

	origTime := s.providerCtx().BlockTime()

	// delegate bondAmt and undelegate all of it
	initBalance, valsetUpdateID := bondAndUnbond(s, delAddr, bondAmt, 1)

	// check that staking unbonding op was created and onHold is true
	checkStakingUnbondingOps(s, 1, true, true)

	// check that CCV unbonding op was created
	checkCCVUnbondingOp(s, s.providerCtx(), s.consumerChain.ChainID, valsetUpdateID, true)

	channelID := s.path.EndpointB.ChannelID

	// save next sequence before sending a packet
	seq, ok := s.providerChain.App.GetIBCKeeper().ChannelKeeper.GetNextSequenceSend(s.providerCtx(), providertypes.PortID, channelID)
	s.Require().True(ok)

	// SEND PACKET
	s.providerChain.App.EndBlock(abci.RequestEndBlock{})

	// verify that the packet was sent
	commit := s.providerChain.App.GetIBCKeeper().ChannelKeeper.GetPacketCommitment(s.providerCtx(), providertypes.PortID, channelID, seq)
	s.Require().NotNil(commit, "did not find packet commitment")

	// Get validator update created in Endblock to use in reconstructing packet
	valUpdates := s.providerChain.App.(*appProvider.App).StakingKeeper.GetValidatorUpdates(s.providerCtx())

	// Get current blocktime
	oldBlockTime := s.providerCtx().BlockTime()

	// commit block on provider chain and update consumer chain's client
	commitProviderBlock(s)
	// Relay packet to consumer chain
	packet, packetData := sendValUpdatePacket(s, valUpdates, valsetUpdateID, oldBlockTime, 1)

	// CHECK THAT UNBONDING IS NOT COMPLETE
	// Check that unbonding has not yet completed. The initBalance is still lower
	// by the bond amount, because it has been taken out of the delegator's account
	s.Require().True(getBalance(s, s.providerCtx(), delAddr).Equal(initBalance.Sub(bondAmt)))

	// END CONSUMER UNBONDING
	// end consumer's unbonding period by advancing time and calling UnbondMaturePackets
	endConsumerUnbondingPeriod(s, origTime)

	// commit block on consumer and update provider client
	commitConsumerBlock(s)

	// send acknowledgement to provider
	sendValUpdateAck(s, s.providerCtx(), packet, packetData)

	// END PROVIDER UNBONDING
	newProviderCtx := endProviderUnbondingPeriod(s, origTime)

	// CHECK THAT UNBONDING IS COMPLETE
	// Check that ccv unbonding op has been deleted
	checkCCVUnbondingOp(s, newProviderCtx, s.consumerChain.ChainID, valsetUpdateID, false)

	// Check that staking unbonding op has been deleted
	checkStakingUnbondingOps(s, valsetUpdateID, false, false)

	// Check that the coins have been returned
	s.Require().True(getBalance(s, newProviderCtx, delAddr).Equal(initBalance))
}

func (s *ProviderTestSuite) TestUndelegationDuringInit() {
	// start CCV channel setup
	fmt.Printf("BEFORE StartSetupCCVChannel\n")
	s.StartSetupCCVChannel()
	fmt.Printf("!!!!!!! AFTER  StartSetupCCVChannel\n\n")

	for i := 0; i < len(s.providerChain.Vals.Validators); i++ {
		validator, _ := s.getVal(i)
		consAddr, _ := validator.GetConsAddr()
		fmt.Printf("  >  val#%d [%s] w/ tokens %d\n", i, consAddr, validator.GetTokens().Int64())
	}

	// delegate bondAmt and undelegate half of it
	bondAmt := sdk.NewInt(10000000)
	delAddr := s.providerChain.SenderAccount.GetAddress()
	initBalance, valsetUpdateID := bondAndUnbond(s, delAddr, bondAmt, 2)
	fmt.Printf("bondAndUnbond vscID=%d\n", valsetUpdateID)

	// check that staking unbonding op was created and onHold is true
	checkStakingUnbondingOps(s, 1, true, true)

	// check that CCV unbonding op was created
	checkCCVUnbondingOp(s, s.providerCtx(), s.consumerChain.ChainID, valsetUpdateID, true)

	// call NextBlock on the provider (which increments the height)
	s.providerChain.NextBlock()

	// check that the VSC packet is stored in state as pending
	pendingVSCs := s.providerChain.App.(*appProvider.App).ProviderKeeper.GetPendingVSCs(s.providerCtx(), s.consumerChain.ChainID)
	s.Require().True(len(pendingVSCs) == 1, "no pending VSC packet found")

	fmt.Printf(">>> AFTER  NextBlock\n")

	// increment time so that the unbonding period ends on the provider
	incrementTimeByProviderUnbondingPeriod(s)

	fmt.Printf(">>> AFTER  END PROVIDER UNBONDING\n")

	for i := 0; i < len(s.providerChain.Vals.Validators); i++ {
		validator, _ := s.getVal(i)
		consAddr, _ := validator.GetConsAddr()
		fmt.Printf("  >  val#%d [%s] w/ tokens %d\n", i, consAddr, validator.GetTokens().Int64())
	}

	// check that the unbonding op is still there and onHold is true
	checkStakingUnbondingOps(s, 1, true, true)

	// Check that unbonding has not yet completed. The initBalance is still lower
	// by the bond amount, because it has been taken out of the delegator's account
	s.Require().True(getBalance(s, s.providerCtx(), delAddr).Equal(initBalance.Sub(bondAmt)))

	// complete CCV channel setup
	// fmt.Printf("\nBEFORE CompleteSetupCCVChannel\n")
	// s.CompleteSetupCCVChannel()
	// fmt.Printf("!!!!!!! AFTER  CompleteSetupCCVChannel\n\n")

	fmt.Printf("$$$ BEFORE ChanOpenAck\n")
	err := s.path.EndpointA.ChanOpenAck()
	s.Require().NoError(err)
	fmt.Printf("$$$ AFTER ChanOpenAck\n")
	fmt.Printf("$$$ BEFORE ChanOpenConfirm\n")
	err = s.path.EndpointB.ChanOpenConfirm()
	s.Require().NoError(err)
	fmt.Printf("$$$ AFTER ChanOpenConfirm\n")
	timeoutBlockTime := s.providerCtx().BlockTime().Add(-ibctesting.TimeIncrement).UTC()
	fmt.Printf("timeoutBlockTime=%s\n\n", timeoutBlockTime.String())
	s.path.EndpointA.UpdateClient()

	// check that the VSC packets were committed in the provider's state
	channelID := s.path.EndpointB.ChannelID
	commitments := s.providerChain.App.GetIBCKeeper().ChannelKeeper.GetAllPacketCommitmentsAtChannel(s.providerCtx(), providertypes.PortID, channelID)
	s.Require().True(len(commitments) == 1, "did not find packet commitment")

	// RELAY PACKET
	// - create packet
	commitment := commitments[0]
	packet := channeltypes.NewPacket(
		pendingVSCs[0].GetBytes(),
		commitment.Sequence,
		providertypes.PortID,
		s.path.EndpointB.ChannelID,
		consumertypes.PortID,
		s.path.EndpointA.ChannelID,
		clienttypes.Height{},
		uint64(ccv.GetTimeoutTimestamp(timeoutBlockTime).UnixNano()),
	)
	// - relay the packet
	fmt.Printf("BEFORE   RELAY PACKET\n")
	err = s.RelayPacketWithoutAck(packet)
	s.Require().NoError(err)

	fmt.Printf("\nAFTER   RELAY PACKET\n")

	// update consumer chain hist info
	s.UpdateConsumerHistInfo(pendingVSCs[0].ValidatorUpdates)

	// call NextBlock on the provider (which increments the height)
	s.consumerChain.NextBlock()

	// END CONSUMER UNBONDING
	// - increment time so that the unbonding period ends on the consumer
	incrementTimeByConsumerUnbondingPeriod(s)
	// // - send acknowledgement to provider
	// ack := channeltypes.NewResultAcknowledgement([]byte{byte(1)})
	// err := s.path.EndpointA.AcknowledgePacket(packet, ack.Acknowledgement())
	// s.Require().NoError(err)

	// CHECK THAT UNBONDING IS COMPLETE
	// - check that ccv unbonding op has been deleted
	checkCCVUnbondingOp(s, s.providerCtx(), s.consumerChain.ChainID, valsetUpdateID, false)
	// - check that staking unbonding op has been deleted
	checkStakingUnbondingOps(s, valsetUpdateID, false, false)
	// - check that the coins have been returned
	s.Require().True(getBalance(s, s.providerCtx(), delAddr).Equal(initBalance))
}

// TODO FIX, the consumer is added during SetupTest()
// Bond some tokens on provider
// Unbond them to create unbonding op
// Check unbonding ops on both sides
// Advance time so that provider's unbonding op completes
// Check that unbonding has completed in provider staking
func (s *ProviderTestSuite) TestUnbondingNoConsumer() {
	origTime := s.providerCtx().BlockTime()

	bondAmt := sdk.NewInt(10000000)
	delAddr := s.providerChain.SenderAccount.GetAddress()
	// delegate bondAmt and undelegate 1/2 of it
	initBalance, valsetUpdateID := bondAndUnbond(s, delAddr, bondAmt, 2)

	// check that staking unbonding op was created and onHold is false
	checkStakingUnbondingOps(s, 1, true, false)

	// check that CCV unbonding op was not created
	checkCCVUnbondingOp(s, s.providerCtx(), s.consumerChain.ChainID, valsetUpdateID, false)

	// END PROVIDER UNBONDING
	newProviderCtx := endProviderUnbondingPeriod(s, origTime)

	// CHECK THAT UNBONDING IS COMPLETE
	// Check that staking unbonding op has been deleted
	checkStakingUnbondingOps(s, valsetUpdateID, false, false)

	// Check that half the coins have been returned
	s.Require().True(getBalance(s, newProviderCtx, delAddr).Equal(initBalance.Sub(bondAmt.Quo(sdk.NewInt(2)))))
}

func getBalance(s *ProviderTestSuite, providerCtx sdk.Context, delAddr sdk.AccAddress) sdk.Int {
	return s.providerChain.App.(*appProvider.App).BankKeeper.GetBalance(providerCtx, delAddr, s.providerBondDenom()).Amount
}

// bondAndUnbond delegates bondAmt from delAddr to the first validator
// and then immediately undelegates 1/shareDiv of that delegation
func bondAndUnbond(s *ProviderTestSuite, delAddr sdk.AccAddress, bondAmt sdk.Int, shareDiv int64) (initBalance sdk.Int, valsetUpdateId uint64) {
	initBalance = getBalance(s, s.providerCtx(), delAddr)

	// Choose a validator, and get its address and data structure into the correct types
	validator, valAddr := s.getVal(0)

	// INITIAL BOND
	// Bond some tokens on provider to change validator powers
	shares, err := s.providerChain.App.(*appProvider.App).StakingKeeper.Delegate(s.providerCtx(), delAddr, bondAmt, stakingtypes.Unbonded, stakingtypes.Validator(validator), true)
	s.Require().NoError(err)

	// Check that the correct number of tokens were taken out of the delegator's account
	s.Require().True(getBalance(s, s.providerCtx(), delAddr).Equal(initBalance.Sub(bondAmt)))

	// UNDELEGATE
	// Undelegate half
	_, err = s.providerChain.App.(*appProvider.App).StakingKeeper.Undelegate(s.providerCtx(), delAddr, valAddr, shares.QuoInt64(shareDiv))
	s.Require().NoError(err)

	// Check that the tokens have not been returned yet
	s.Require().True(getBalance(s, s.providerCtx(), delAddr).Equal(initBalance.Sub(bondAmt)))

	// save the current valset update ID
	valsetUpdateID := s.providerChain.App.(*appProvider.App).ProviderKeeper.GetValidatorSetUpdateId(s.providerCtx())

	return initBalance, valsetUpdateID
}

// incrementTimeByProviderUnbondingPeriod increments the overall time by
// the unbonding period on the provider; note that it is expected for this
// period to be larger than the unbonding period on the consumer
func incrementTimeByProviderUnbondingPeriod(s *ProviderTestSuite) {
	// Get unboding period from staking keeper
	providerUnbondingPeriod := s.providerChain.App.GetStakingKeeper().UnbondingTime(s.providerCtx())
	consumerUnbondingPeriod, found := s.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetUnbondingTime(s.consumerCtx())
	s.Require().True(found)
	s.Require().True(consumerUnbondingPeriod == providerUnbondingPeriod-24*time.Hour)
	// Make sure the clients do not expire
	jumpPeriod := providerUnbondingPeriod/4 + time.Hour
	for i := 0; i < 4; i++ {
		s.coordinator.IncrementTimeBy(jumpPeriod)
		// Update the provider client on the consumer
		s.path.EndpointA.UpdateClient()
		// Update the consumer client on the provider
		s.path.EndpointB.UpdateClient()
	}
}

// incrementTimeByConsumerUnbondingPeriod increments the overall time by
// the unbonding period on the consumer; note that it is expected for this
// period to be one day shorter than the unbonding period on the provider
func incrementTimeByConsumerUnbondingPeriod(s *ProviderTestSuite) {
	// Get unboding period from consumer keeper
	consumerUnbondingPeriod, found := s.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetUnbondingTime(s.consumerCtx())
	s.Require().True(found)
	// Check that the unboding period is ideed one day less than
	// the unbonding period on the provider
	providerUnbondingPeriod := s.providerChain.App.GetStakingKeeper().UnbondingTime(s.providerCtx())
	s.Require().True(consumerUnbondingPeriod == providerUnbondingPeriod-24*time.Hour)
	// Make sure the clients do not expire
	jumpPeriod := consumerUnbondingPeriod/4 + time.Hour
	for i := 0; i < 4; i++ {
		s.coordinator.IncrementTimeBy(jumpPeriod)
		// Update the provider client on the consumer
		fmt.Println("< Update provider client >")
		s.path.EndpointA.UpdateClient()
		// Update the consumer client on the provider
		trustedHeight := s.providerChain.GetClientState(s.path.EndpointB.ClientID).GetLatestHeight().(clienttypes.Height)
		fmt.Printf("< Update consumer client > trustedHeight: %d, H: %d\n", trustedHeight.RevisionHeight, s.consumerCtx().BlockHeight())
		s.path.EndpointB.UpdateClient()
	}
}

func endProviderUnbondingPeriod(s *ProviderTestSuite, origTime time.Time) sdk.Context {
	// - End provider unbonding period
	sk := s.providerChain.App.(*appProvider.App).StakingKeeper
	unbondingPeriod := sk.UnbondingTime(s.providerCtx())
	providerCtx := s.providerCtx().WithBlockTime(origTime.Add(unbondingPeriod).Add(3 * time.Hour))
	// s.providerChain.App.EndBlock(abci.RequestEndBlock{}) // <- this doesn't work because we can't modify the ctx
	sk.BlockValidatorUpdates(providerCtx)

	return providerCtx
}

func endConsumerUnbondingPeriod(s *ProviderTestSuite, origTime time.Time) {
	// - End consumer unbonding period
	unbondingPeriod, found := s.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetUnbondingTime(s.consumerCtx())
	s.Require().True(found)
	consumerCtx := s.consumerCtx().WithBlockTime(origTime.Add(unbondingPeriod).Add(3 * time.Hour))
	// s.consumerChain.App.EndBlock(abci.RequestEndBlock{}) // <- this doesn't work because we can't modify the ctx
	err := s.consumerChain.App.(*appConsumer.App).ConsumerKeeper.UnbondMaturePackets(consumerCtx)
	s.Require().NoError(err)
}

func checkStakingUnbondingOps(s *ProviderTestSuite, id uint64, found bool, onHold bool) {
	stakingUnbondingOp, wasFound := GetStakingUnbondingDelegationEntry(s.providerCtx(), s.providerChain.App.(*appProvider.App).StakingKeeper, id)
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

func sendValUpdatePacket(s *ProviderTestSuite, valUpdates []abci.ValidatorUpdate, valUpdateId uint64, blockTime time.Time, packetSequence uint64) (channeltypes.Packet, types.ValidatorSetChangePacketData) {
	packetData := types.NewValidatorSetChangePacketData(valUpdates, valUpdateId, nil)
	timeout := uint64(ccv.GetTimeoutTimestamp(blockTime).UnixNano())
	packet := channeltypes.NewPacket(packetData.GetBytes(), packetSequence, providertypes.PortID, s.path.EndpointB.ChannelID,
		consumertypes.PortID, s.path.EndpointA.ChannelID, clienttypes.Height{}, timeout)

	// Receive CCV packet on consumer chain
	err := s.path.EndpointA.RecvPacket(packet)
	s.Require().NoError(err)

	return packet, packetData
}

func commitProviderBlock(s *ProviderTestSuite) {
	s.coordinator.CommitBlock(s.providerChain)
	err := s.path.EndpointA.UpdateClient()
	s.Require().NoError(err)
}

func commitConsumerBlock(s *ProviderTestSuite) {
	// commit consumer chain and update provider chain client
	s.coordinator.CommitBlock(s.consumerChain)
	err := s.path.EndpointB.UpdateClient()
	s.Require().NoError(err)
}

func sendValUpdateAck(s *ProviderTestSuite, providerCtx sdk.Context, packet channeltypes.Packet, packetData types.ValidatorSetChangePacketData) {
	// TODO: I have commented out the below code because i do not know how to
	// get s.path.EndpointB.AcknowledgePacket to see the correct time. Instead, I am calling the
	// CCV module's keeper function directly. This is not as complete of a test.
	// If we have a more robust time system at some point, use s.path.EndpointB.AcknowledgePacket again.

	ack := channeltypes.NewResultAcknowledgement([]byte{byte(1)})
	// err := s.path.EndpointB.AcknowledgePacket(packet, ack.Acknowledgement())
	// s.Require().NoError(err)

	err := s.providerChain.App.(*appProvider.App).ProviderKeeper.OnAcknowledgementPacket(providerCtx, packet, packetData, ack)
	s.Require().NoError(err)
}

func GetStakingUnbondingDelegationEntry(ctx sdk.Context, k stakingkeeper.Keeper, id uint64) (stakingUnbondingOp stakingtypes.UnbondingDelegationEntry, found bool) {
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

// RelayPacket attempts to relay the packet first on EndpointA and then on EndpointB
// if EndpointA does not contain a packet commitment for that packet. An error is returned
// if a relay step fails or the packet commitment does not exist on either endpoint.
func (s *ProviderTestSuite) RelayPacketWithoutAck(packet channeltypes.Packet) error {
	pc := s.path.EndpointA.Chain.App.GetIBCKeeper().ChannelKeeper.GetPacketCommitment(s.path.EndpointA.Chain.GetContext(), packet.GetSourcePort(), packet.GetSourceChannel(), packet.GetSequence())
	if bytes.Equal(pc, channeltypes.CommitPacket(s.path.EndpointA.Chain.App.AppCodec(), packet)) {

		// packet found, relay from A to B
		s.path.EndpointB.UpdateClient()

		err := s.path.EndpointB.RecvPacket(packet)
		if err != nil {
			return err
		}

		return nil
	}

	pc = s.path.EndpointB.Chain.App.GetIBCKeeper().ChannelKeeper.GetPacketCommitment(s.path.EndpointB.Chain.GetContext(), packet.GetSourcePort(), packet.GetSourceChannel(), packet.GetSequence())
	if bytes.Equal(pc, channeltypes.CommitPacket(s.path.EndpointB.Chain.App.AppCodec(), packet)) {

		// packet found, relay B to A
		s.path.EndpointA.UpdateClient()

		err := s.path.EndpointA.RecvPacket(packet)
		if err != nil {
			return err
		}

		return nil
	}

	return fmt.Errorf("packet commitment does not exist on either endpoint for provided packet")
}
