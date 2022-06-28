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
	"github.com/cosmos/interchain-security/x/ccv/utils"

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
	initBalance, valsetUpdateID := delegateAndUndelegate(s, delAddr, bondAmt, 2)

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
	initBalance, valsetUpdateID := delegateAndUndelegate(s, delAddr, bondAmt, 2)

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

// TestUndelegationEdgeCase checks that an unbonding operation completes
// even when the validator set is not changed
func (s *ProviderTestSuite) TestUndelegationEdgeCase() {
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

	// relay VSC packets from provider to consumer
	relayAllCommittedPackets(s, s.providerChain, s.path, providertypes.PortID, s.path.EndpointB.ChannelID, 1)

	// check that the unbonding is not complete
	s.Require().True(getBalance(s, s.providerCtx(), delAddr).Equal(initBalance.Sub(bondAmt)))

	// increment time so that the unbonding period ends on the consumer
	incrementTimeByUnbondingPeriod(s, false)

	// relay VSCMatured packets from consumer to provider
	relayAllCommittedPackets(s, s.consumerChain, s.path, consumertypes.PortID, s.path.EndpointA.ChannelID, 1)

	// increment time so that the unbonding period ends on the provider
	incrementTimeByUnbondingPeriod(s, true)

	// check that the unbonding operation completed
	// - check that ccv unbonding op has been deleted
	checkCCVUnbondingOp(s, s.providerCtx(), s.consumerChain.ChainID, valsetUpdateID, false)
	// - check that staking unbonding op has been deleted
	checkStakingUnbondingOps(s, valsetUpdateID, false, false)
	// - check that one quarter the delegated coins have been returned
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
	pendingVSCs := s.providerChain.App.(*appProvider.App).ProviderKeeper.GetPendingVSCs(s.providerCtx(), s.consumerChain.ChainID)
	s.Require().True(len(pendingVSCs) == 1, "no pending VSC packet found")

	// delegate again to create another VSC packet
	delegate(s, delAddr, bondAmt)

	// call NextBlock on the provider (which increments the height)
	s.providerChain.NextBlock()

	// check that the VSC packet is stored in state as pending
	pendingVSCs = s.providerChain.App.(*appProvider.App).ProviderKeeper.GetPendingVSCs(s.providerCtx(), s.consumerChain.ChainID)
	s.Require().True(len(pendingVSCs) == 2, "only one pending VSC packet found")

	// increment time so that the unbonding period ends on the provider
	incrementTimeByUnbondingPeriod(s, true)
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
	incrementTimeByUnbondingPeriod(s, false)

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

// incrementTimeByUnbondingPeriod increments the overall time by
// 	- if provider == true, the unbonding period on the provider;
//	- otherwise, the unbonding period on the consumer.
// Note that it is expected for the provider unbonding period
// to be one day larger than the consumer unbonding period.
func incrementTimeByUnbondingPeriod(s *ProviderTestSuite, provider bool) {
	// Get unboding period from staking keeper
	providerUnbondingPeriod := s.providerChain.App.GetStakingKeeper().UnbondingTime(s.providerCtx())
	consumerUnbondingPeriod, found := s.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetUnbondingTime(s.consumerCtx())
	s.Require().True(found)
	expectedUnbondingPeriod := utils.ComputeConsumerUnbondingPeriod(providerUnbondingPeriod)
	s.Require().True(expectedUnbondingPeriod == providerUnbondingPeriod-24*time.Hour)
	s.Require().True(consumerUnbondingPeriod == expectedUnbondingPeriod)
	var jumpPeriod time.Duration
	if provider {
		jumpPeriod = providerUnbondingPeriod
	} else {
		jumpPeriod = consumerUnbondingPeriod
	}
	// Make sure the clients do not expire
	jumpPeriod = jumpPeriod/4 + time.Hour
	for i := 0; i < 4; i++ {
		s.coordinator.IncrementTimeBy(jumpPeriod)
		// Update the provider client on the consumer
		s.path.EndpointA.UpdateClient()
		// Update the consumer client on the provider
		s.path.EndpointB.UpdateClient()
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
	s.Require().True(len(commitments) == expectedPackets, "did not find packet commitments")

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

	err := s.providerChain.App.(*appProvider.App).ProviderKeeper.OnAcknowledgementPacket(providerCtx, packet, ack)
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
	pc := s.path.EndpointA.Chain.App.GetIBCKeeper().ChannelKeeper.GetPacketCommitment(
		s.path.EndpointA.Chain.GetContext(),
		packet.GetSourcePort(),
		packet.GetSourceChannel(),
		packet.GetSequence(),
	)
	if bytes.Equal(pc, channeltypes.CommitPacket(s.path.EndpointA.Chain.App.AppCodec(), packet)) {
		// packet found, relay from A to B
		s.path.EndpointB.UpdateClient()

		err := s.path.EndpointB.RecvPacket(packet)
		if err != nil {
			return err
		}

		return nil
	}

	pc = s.path.EndpointB.Chain.App.GetIBCKeeper().ChannelKeeper.GetPacketCommitment(
		s.path.EndpointB.Chain.GetContext(),
		packet.GetSourcePort(),
		packet.GetSourceChannel(),
		packet.GetSequence(),
	)
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
