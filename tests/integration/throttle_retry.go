package integration

import (
	"bytes"
	"time"

	channeltypes "github.com/cosmos/ibc-go/v7/modules/core/04-channel/types"

	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	ccvtypes "github.com/cosmos/interchain-security/v3/x/ccv/types"
)

// TestSlashRetries tests the throttling v2 retry logic at an integration level.
//
// TODO: can prob make some helpers to make this test more readable and succinct. Matching vals for example
func (s *CCVTestSuite) TestSlashRetries() {
	s.SetupAllCCVChannels()
	s.SendEmptyVSCPacket() // Establish ccv channel
	s.setupValidatorPowers()

	//
	// Provider setup
	//
	providerKeeper := s.providerApp.GetProviderKeeper()
	// Initialize slash meter
	providerKeeper.InitializeSlashMeter(s.providerCtx())
	// Assert that we start out with no jailings
	providerStakingKeeper := s.providerApp.GetTestStakingKeeper()
	vals := providerStakingKeeper.GetAllValidators(s.providerCtx())
	for _, val := range vals {
		s.Require().False(val.IsJailed())
	}
	// Setup signing info for jailings
	tmval1 := s.providerChain.Vals.Validators[1]
	tmval2 := s.providerChain.Vals.Validators[2]
	s.setDefaultValSigningInfo(*tmval1)
	s.setDefaultValSigningInfo(*tmval2)

	//
	// Consumer setup
	//
	consumerKeeper := s.getFirstBundle().App.GetConsumerKeeper()
	// Assert no slash record exists
	_, found := consumerKeeper.GetSlashRecord(s.consumerCtx())
	s.Require().False(found)

	//
	// Test section: See FSM explanation in throttle_retry.go
	//

	// Construct a mock slash packet from consumer
	packet1, data := s.constructSlashPacketFromConsumerWithData(s.getFirstBundle(), *tmval1, stakingtypes.Infraction_INFRACTION_DOWNTIME, 1)

	// Append packet to be sent by consumer
	consumerKeeper.AppendPendingPacket(s.consumerCtx(), ccvtypes.SlashPacket,
		&ccvtypes.ConsumerPacketData_SlashPacketData{
			SlashPacketData: &data,
		},
	)

	sendTime := s.consumerCtx().BlockTime()

	// Advance block on consumer to send pending packet
	s.getFirstBundle().Chain.NextBlock()

	// Confirm packet was sent via state that's updated on send
	slashRecord, found := consumerKeeper.GetSlashRecord(s.consumerCtx())
	s.Require().True(found)
	s.Require().True(slashRecord.WaitingOnReply)
	s.Require().NotZero(slashRecord.SendTime)
	s.Require().Equal(sendTime, slashRecord.SendTime)
	s.Require().Len(consumerKeeper.GetPendingPackets(s.consumerCtx()), 1)

	// Packet sending blocked until provider returns slash packet handled ack
	s.Require().False(consumerKeeper.PacketSendingPermitted(s.consumerCtx()))

	// Recv packet on provider.
	relayAllCommittedPackets(s, s.consumerChain, s.path, ccvtypes.ConsumerPortID, s.path.EndpointA.ChannelID, 1)

	// Couple blocks pass on provider for provider staking keeper to process jailing
	s.providerChain.NextBlock()
	s.providerChain.NextBlock()

	// Default slash meter replenish fraction is 0.05, so packet should be handled on provider.
	vals = s.providerApp.GetTestStakingKeeper().GetAllValidators(s.providerCtx())

	// Match val from staking keeper to tmval1
	var stakingVal1 stakingtypes.Validator
	for i, val := range vals {
		consAddr, err := val.GetConsAddr()
		s.Require().NoError(err)
		if bytes.Equal(consAddr.Bytes(), tmval1.Address.Bytes()) {
			stakingVal1 = vals[i]
		}
	}
	// Require stakingVal1 is found
	s.Require().NotZero(stakingVal1)

	s.Require().True(stakingVal1.IsJailed())
	s.Require().Equal(int64(0),
		s.providerApp.GetTestStakingKeeper().GetLastValidatorPower(s.providerCtx(), stakingVal1.GetOperator()))

	// Now slash meter should be negative on provider
	s.Require().True(s.providerApp.GetProviderKeeper().GetSlashMeter(s.providerCtx()).IsNegative())

	// Apply ack back on consumer
	expectedAck := channeltypes.NewResultAcknowledgement([]byte(ccvtypes.SlashPacketHandledResult))
	err := s.getFirstBundle().Path.EndpointA.AcknowledgePacket(packet1, expectedAck.Acknowledgement())
	s.Require().NoError(err)

	// Slash record should have been deleted, head of pending packets should have been popped,
	// since provider has handled the packet.
	_, found = consumerKeeper.GetSlashRecord(s.consumerCtx())
	s.Require().False(found)
	s.Require().Empty(consumerKeeper.GetPendingPackets(s.consumerCtx()))

	// Packet sending should now be unblocked
	s.Require().True(consumerKeeper.PacketSendingPermitted(s.consumerCtx()))

	// pass two blocks on provider and consumer for good measure
	s.providerChain.NextBlock()
	s.providerChain.NextBlock()
	s.consumerChain.NextBlock()
	s.consumerChain.NextBlock()

	// Have consumer queue a new slash packet for a different validator.
	packet2, data := s.constructSlashPacketFromConsumerWithData(
		s.getFirstBundle(), *tmval2, stakingtypes.Infraction_INFRACTION_DOWNTIME, 1)
	consumerKeeper.AppendPendingPacket(s.consumerCtx(), ccvtypes.SlashPacket,
		&ccvtypes.ConsumerPacketData_SlashPacketData{
			SlashPacketData: &data,
		},
	)

	// Advance block on consumer to send pending packet
	sendTime = s.consumerCtx().BlockTime()
	s.getFirstBundle().Chain.NextBlock()

	// Confirm packet was sent via state that's updated on send
	slashRecord, found = consumerKeeper.GetSlashRecord(s.consumerCtx())
	s.Require().True(found)
	s.Require().True(slashRecord.WaitingOnReply)
	s.Require().NotZero(slashRecord.SendTime)
	s.Require().Equal(sendTime, slashRecord.SendTime)
	s.Require().Len(consumerKeeper.GetPendingPackets(s.consumerCtx()), 1)

	// Packet sending blocked until provider returns slash packet handled ack
	s.Require().False(consumerKeeper.PacketSendingPermitted(s.consumerCtx()))

	// Recv 2nd packet on provider.
	relayAllCommittedPackets(s, s.consumerChain, s.path, ccvtypes.ConsumerPortID, s.path.EndpointA.ChannelID, 1)

	// Couple blocks pass on provider for staking keeper to process jailings
	s.providerChain.NextBlock()
	s.providerChain.NextBlock()

	vals = s.providerApp.GetTestStakingKeeper().GetAllValidators(s.providerCtx())

	// Match val from staking keeper to tmval2
	var stakingVal2 stakingtypes.Validator
	for i, val := range vals {
		consAddr, err := val.GetConsAddr()
		s.Require().NoError(err)
		if bytes.Equal(consAddr.Bytes(), tmval2.Address.Bytes()) {
			stakingVal2 = vals[i]
		}
	}
	// Require stakingVal2 is found
	s.Require().NotZero(stakingVal2)

	// Val 2 shouldn't be jailed on provider. Slash packet should have been bounced.
	s.Require().False(stakingVal2.IsJailed())
	s.Require().Equal(int64(1000),
		providerStakingKeeper.GetLastValidatorPower(s.providerCtx(), stakingVal2.GetOperator()))

	// Apply ack on consumer
	expectedAck = channeltypes.NewResultAcknowledgement([]byte(ccvtypes.SlashPacketBouncedResult))
	err = s.getFirstBundle().Path.EndpointA.AcknowledgePacket(packet2, expectedAck.Acknowledgement())
	s.Require().NoError(err)

	// Now consumer should have updated it's slash record on receipt of bounce ack
	slashRecord, found = consumerKeeper.GetSlashRecord(s.consumerCtx())
	s.Require().True(found)
	s.Require().False(slashRecord.WaitingOnReply)
	// Packet still at head of queue
	s.Require().Len(consumerKeeper.GetPendingPackets(s.consumerCtx()), 1)

	// Packet sending should still be blocked, WaitingOnReply is false,
	// but retry delay hasn't passed yet.
	s.Require().False(consumerKeeper.PacketSendingPermitted(s.consumerCtx()))

	// IBC testing framework doesn't have a way to advance time,
	// so we manually mutate send time in the slash record to be in the past.
	slashRecord.SendTime = slashRecord.SendTime.Add(-time.Hour - time.Minute)
	consumerKeeper.SetSlashRecord(s.consumerCtx(), slashRecord)

	s.Require().True(consumerKeeper.PacketSendingPermitted(s.consumerCtx()))

	// Set slash meter on provider to positive value,
	// now allowing handling of the slash packet
	providerKeeper.InitializeSlashMeter(s.providerCtx())

	// Advance block on consumer, now consumer should retry the sending of the slash packet.
	sendTime = s.consumerCtx().BlockTime()
	s.getFirstBundle().Chain.NextBlock()

	// Confirm packet was sent via state that's updated on send
	slashRecord, found = consumerKeeper.GetSlashRecord(s.consumerCtx())
	s.Require().True(found)
	s.Require().True(slashRecord.WaitingOnReply)
	s.Require().NotZero(slashRecord.SendTime)
	s.Require().Equal(sendTime, slashRecord.SendTime)
	s.Require().Len(consumerKeeper.GetPendingPackets(s.consumerCtx()), 1)

	// Recv retried packet on provider.
	relayAllCommittedPackets(s, s.consumerChain, s.path, ccvtypes.ConsumerPortID, s.path.EndpointA.ChannelID, 1)

	// Couple blocks pass on provider for provider staking keeper to process jailing
	s.providerChain.NextBlock()
	s.providerChain.NextBlock()

	vals = s.providerApp.GetTestStakingKeeper().GetAllValidators(s.providerCtx())

	// Match val from staking keeper to tmval2
	stakingVal2 = stakingtypes.Validator{}
	for i, val := range vals {
		consAddr, err := val.GetConsAddr()
		s.Require().NoError(err)
		if bytes.Equal(consAddr.Bytes(), tmval2.Address.Bytes()) {
			stakingVal2 = vals[i]
		}
	}
	// Require stakingVal2 is found
	s.Require().NotZero(stakingVal2)

	// Provider should have now jailed val[2]
	vals = s.providerApp.GetTestStakingKeeper().GetAllValidators(s.providerCtx())
	s.Require().True(stakingVal2.IsJailed())
	s.Require().Equal(int64(0),
		s.providerApp.GetTestStakingKeeper().GetLastValidatorPower(s.providerCtx(), stakingVal2.GetOperator()))
}
