package integration

import (
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	channeltypes "github.com/cosmos/ibc-go/v7/modules/core/04-channel/types"
	provider "github.com/cosmos/interchain-security/v3/x/ccv/provider"
	providertypes "github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v3/x/ccv/types"
)

// Note we don't fully test IBC integration in favor of being able to test ack results better
//
// See FSM explanation in throttle_retry.go
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
	// Test section
	//

	// Construct a mock slash packet from consumer
	tmval1 := s.providerChain.Vals.Validators[1]
	packet1 := s.constructSlashPacketFromConsumer(s.getFirstBundle(), *tmval1, stakingtypes.Infraction_INFRACTION_DOWNTIME, 1)

	// Mock the sending of the packet on consumer
	consumerKeeper.AppendPendingPacket(s.consumerCtx(), ccvtypes.SlashPacket,
		&ccvtypes.ConsumerPacketData_SlashPacketData{
			SlashPacketData: &ccvtypes.SlashPacketData{},
		},
	)
	consumerKeeper.UpdateSlashRecordOnSend(s.consumerCtx())
	s.Require().Len(consumerKeeper.GetPendingPackets(s.consumerCtx()), 1)

	// Recv packet on provider and assert ack. Provider should return no-op result since packet is handled.
	ack := providerModule.OnRecvPacket(s.providerCtx(), packet1, nil)
	expectedNoOpAck := channeltypes.NewResultAcknowledgement([]byte(ccvtypes.NoOpResult))
	s.Require().Equal(expectedNoOpAck.Acknowledgement(), ack.Acknowledgement())

	// Couple blocks pass on provider for staking keeper to process jailing
	s.providerChain.NextBlock()
	s.providerChain.NextBlock()

	// Default slash meter replenish fraction is 0.05, so packet should be handled on provider.
	vals = s.providerApp.GetTestStakingKeeper().GetAllValidators(s.providerCtx())
	s.Require().True(vals[1].IsJailed())
	s.Require().Equal(int64(0),
		s.providerApp.GetTestStakingKeeper().GetLastValidatorPower(s.providerCtx(), vals[1].GetOperator()))

	// Now slash meter should be negative on provider
	s.Require().True(s.providerApp.GetProviderKeeper().GetSlashMeter(s.providerCtx()).IsNegative())

	// Apply ack back on consumer
	ackForConsumer := expectedNoOpAck
	err := consumerKeeper.OnAcknowledgementPacket(s.consumerCtx(), packet1, ackForConsumer)
	s.Require().NoError(err)

	// Slash record should have been deleted, head of pending packets should have been popped
	_, found = consumerKeeper.GetSlashRecord(s.consumerCtx())
	s.Require().False(found)
	s.Require().Empty(consumerKeeper.GetPendingPackets(s.consumerCtx()))

	// Construct and mock the sending of a second packet on consumer
	tmval2 := s.providerChain.Vals.Validators[2]
	packet2 := s.constructSlashPacketFromConsumer(s.getFirstBundle(), *tmval2, stakingtypes.Infraction_INFRACTION_DOWNTIME, 1)

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

	// Recv 2nd slash packet on provider for different validator.
	// Provider should return bounce result since packet is not handled.
	ack = providerModule.OnRecvPacket(s.providerCtx(), packet2, nil)
	expectedBouncedAck := channeltypes.NewResultAcknowledgement([]byte(ccvtypes.SlashPacketBouncedResult))
	s.Require().Equal(expectedBouncedAck.Acknowledgement(), ack.Acknowledgement())

	// Val shouldn't be jailed on provider
	s.Require().False(vals[2].IsJailed())
	s.Require().Equal(int64(1000),
		providerStakingKeeper.GetLastValidatorPower(s.providerCtx(), vals[2].GetOperator()))

	// Apply ack on consumer
	ackForConsumer = channeltypes.NewResultAcknowledgement(ack.Acknowledgement()) // Shim since provider uses a different type
	err = consumerKeeper.OnAcknowledgementPacket(s.consumerCtx(), packet2, ackForConsumer)
	s.Require().NoError(err)

	// slashRecord.WaitingOnReply should have been updated to false
	slashRecord, found = consumerKeeper.GetSlashRecord(s.consumerCtx())
	s.Require().True(found)
	s.Require().False(slashRecord.WaitingOnReply)

	// Packet still in queue
	s.Require().Len(consumerKeeper.GetPendingPackets(s.consumerCtx()), 1)
}
