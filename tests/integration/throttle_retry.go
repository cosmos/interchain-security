package integration

import (
	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v8/modules/core/04-channel/types"

	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	provider "github.com/cosmos/interchain-security/v3/x/ccv/provider"
	providertypes "github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v3/x/ccv/types"
)

// TestSlashRetries tests the throttling v2 retry logic. Without provider changes,
// the consumer will queue up a slash packet, the provider will return a v1 result,
// and the consumer will never need to retry.
//
// Once provider changes are made (slash packet queuing is removed), the consumer may retry packets
// via new result acks from the provider.
//
// TODO: This test will need updating once provider changes are made.
func (s *CCVTestSuite) TestSlashRetries() {
	s.SetupAllCCVChannels()
	s.setupValidatorPowers()

	//
	// Provider setup
	//
	providerKeeper := s.providerApp.GetProviderKeeper()
	providerModule := provider.NewAppModule(&providerKeeper, s.providerApp.GetSubspace(providertypes.ModuleName))
	// Initialize slash meter
	providerKeeper.InitializeSlashMeter(s.providerCtx())
	// Assert that we start out with no jailings
	providerStakingKeeper := s.providerApp.GetTestStakingKeeper()
	vals := providerStakingKeeper.GetAllValidators(s.providerCtx())
	for _, val := range vals {
		s.Require().False(val.IsJailed())
	}
	// Setup signing info for jailings
	s.setDefaultValSigningInfo(*s.providerChain.Vals.Validators[1])

	//
	// Consumer setup
	//
	consumerKeeper := s.consumerApp.GetConsumerKeeper()
	// Assert no slash record exists
	_, found := consumerKeeper.GetSlashRecord(s.consumerCtx())
	s.Require().False(found)

	//
	// Test section: See FSM explanation in throttle_retry.go
	//

	// Construct a mock slash packet from consumer
	tmval1 := s.providerChain.Vals.Validators[1]
	packetData1 := s.constructSlashPacketFromConsumer(s.getFirstBundle(), *tmval1, stakingtypes.Infraction_INFRACTION_DOWNTIME).GetBytes()
	var (
		timeoutHeight    = clienttypes.Height{}
		timeoutTimestamp = uint64(s.getFirstBundle().GetCtx().BlockTime().Add(ccvtypes.DefaultCCVTimeoutPeriod).UnixNano())
	)
	packet1 := s.newPacketFromConsumer(packetData1, 1, s.getFirstBundle().Path, timeoutHeight, timeoutTimestamp)
	// Mock the sending of the packet on consumer
	consumerKeeper.AppendPendingPacket(s.consumerCtx(), ccvtypes.SlashPacket,
		&ccvtypes.ConsumerPacketData_SlashPacketData{
			SlashPacketData: &ccvtypes.SlashPacketData{},
		},
	)
	consumerKeeper.UpdateSlashRecordOnSend(s.consumerCtx())
	slashRecord, found := consumerKeeper.GetSlashRecord(s.consumerCtx())
	s.Require().True(found)
	s.Require().True(slashRecord.WaitingOnReply)
	s.Require().Len(consumerKeeper.GetPendingPackets(s.consumerCtx()), 1)

	// Recv packet on provider and assert ack. Provider should return v1 result.
	ack := providerModule.OnRecvPacket(s.providerCtx(), packet1, nil)
	expectedv1Ack := channeltypes.NewResultAcknowledgement([]byte(ccvtypes.V1Result))
	s.Require().Equal(expectedv1Ack.Acknowledgement(), ack.Acknowledgement())

	// Couple blocks pass on provider for provider staking keeper to process jailing
	s.providerChain.NextBlock()
	s.providerChain.NextBlock()

	// Default slash meter replenish fraction is 0.05, so packet should be handled on provider.
	vals = s.providerApp.GetTestStakingKeeper().GetAllValidators(s.providerCtx())
	s.Require().True(vals[1].IsJailed())
	s.Require().Equal(int64(0),
		s.providerApp.GetTestStakingKeeper().GetLastValidatorPower(s.providerCtx(), vals[1].GetOperator()))
	s.Require().Equal(uint64(0), providerKeeper.GetThrottledPacketDataSize(s.providerCtx(),
		s.getFirstBundle().Chain.ChainID))

	// Now slash meter should be negative on provider
	s.Require().True(s.providerApp.GetProviderKeeper().GetSlashMeter(s.providerCtx()).IsNegative())

	// Apply ack back on consumer
	ackForConsumer := expectedv1Ack
	err := consumerKeeper.OnAcknowledgementPacket(s.consumerCtx(), packet1, ackForConsumer)
	s.Require().NoError(err)

	// Slash record should have been deleted, head of pending packets should have been popped
	// Since provider has handled the packet
	_, found = consumerKeeper.GetSlashRecord(s.consumerCtx())
	s.Require().False(found)
	s.Require().Empty(consumerKeeper.GetPendingPackets(s.consumerCtx()))

	// pass two blocks on provider and consumer for good measure
	s.providerChain.NextBlock()
	s.providerChain.NextBlock()
	s.consumerChain.NextBlock()
	s.consumerChain.NextBlock()

	// Construct and mock the sending of a second packet on consumer
	tmval2 := s.providerChain.Vals.Validators[2]
	packetData2 := s.constructSlashPacketFromConsumer(s.getFirstBundle(), *tmval2, stakingtypes.Infraction_INFRACTION_DOWNTIME).GetBytes()
	packet2 := s.newPacketFromConsumer(packetData2, 1, s.getFirstBundle().Path, timeoutHeight, timeoutTimestamp)

	consumerKeeper.AppendPendingPacket(s.consumerCtx(), ccvtypes.SlashPacket,
		&ccvtypes.ConsumerPacketData_SlashPacketData{
			SlashPacketData: &ccvtypes.SlashPacketData{},
		},
	)
	consumerKeeper.UpdateSlashRecordOnSend(s.consumerCtx())
	slashRecord, found = consumerKeeper.GetSlashRecord(s.consumerCtx())
	s.Require().True(found)
	s.Require().True(slashRecord.WaitingOnReply)
	s.Require().Len(consumerKeeper.GetPendingPackets(s.consumerCtx()), 1)

	// Recv 2nd slash packet on provider for different validator.
	// Provider should return the same v1 result ack even tho the packet was queued.
	ack = providerModule.OnRecvPacket(s.providerCtx(), packet2, nil)
	expectedv1Ack = channeltypes.NewResultAcknowledgement([]byte(ccvtypes.V1Result))
	s.Require().Equal(expectedv1Ack.Acknowledgement(), ack.Acknowledgement())

	// Couple blocks pass on provider for staking keeper to process jailings
	s.providerChain.NextBlock()
	s.providerChain.NextBlock()

	// Val shouldn't be jailed on provider. Slash packet was queued
	s.Require().False(vals[2].IsJailed())
	s.Require().Equal(int64(1000),
		providerStakingKeeper.GetLastValidatorPower(s.providerCtx(), vals[2].GetOperator()))
	s.Require().Equal(uint64(1), providerKeeper.GetThrottledPacketDataSize(s.providerCtx(),
		s.getFirstBundle().Chain.ChainID))

	// Apply ack on consumer
	ackForConsumer = expectedv1Ack
	err = consumerKeeper.OnAcknowledgementPacket(s.consumerCtx(), packet2, ackForConsumer)
	s.Require().NoError(err)

	// TODO: when provider changes are made, slashRecord.WaitingOnReply should have been updated to false on consumer. Slash Packet will still be in consumer's pending packets queue.

	// Slash record should have been deleted, head of pending packets should have been popped
	// Since provider has handled the packet
	_, found = consumerKeeper.GetSlashRecord(s.consumerCtx())
	s.Require().False(found)
	s.Require().Empty(consumerKeeper.GetPendingPackets(s.consumerCtx()))
}
