package integration

import (
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	channeltypes "github.com/cosmos/ibc-go/v7/modules/core/04-channel/types"
	provider "github.com/cosmos/interchain-security/v3/x/ccv/provider"
	providertypes "github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v3/x/ccv/types"
)

// TODO: more UTs which look at the return values of handlers

// Note we don't fully test IBC integration in favor of being able to test ack results better
func (s *CCVTestSuite) TestSlashRetries() {
	s.SetupAllCCVChannels()
	s.setupValidatorPowers()

	// Initialize slash meter
	s.providerApp.GetProviderKeeper().InitializeSlashMeter(s.providerCtx())

	// Assert that we start out with no jailings
	providerStakingKeeper := s.providerApp.GetTestStakingKeeper()
	vals := providerStakingKeeper.GetAllValidators(s.providerCtx())
	for _, val := range vals {
		s.Require().False(val.IsJailed())
	}

	// Setup signing info for jailings
	s.setDefaultValSigningInfo(*s.providerChain.Vals.Validators[1])

	// Construct slash packet from consumer.
	tmval1 := s.providerChain.Vals.Validators[1]
	packet1 := s.constructSlashPacketFromConsumer(s.getFirstBundle(), *tmval1, stakingtypes.Infraction_INFRACTION_DOWNTIME, 1)

	providerKeeper := s.providerApp.GetProviderKeeper()
	// TODO: helper for module
	providerModule := provider.NewAppModule(&providerKeeper, s.providerApp.GetSubspace(providertypes.ModuleName))

	// Recv packet on provider and assert ack
	ack := providerModule.OnRecvPacket(s.providerCtx(), packet1, nil)
	expectedAckBytes := channeltypes.NewResultAcknowledgement([]byte(ccvtypes.NoOpResult)).Acknowledgement()
	s.Require().Equal(expectedAckBytes, ack.Acknowledgement())

	// Couple blocks pass for staking keeper to process jailing
	s.providerChain.NextBlock()
	s.providerChain.NextBlock()

	// Default slash meter replenish fraction is 0.05, so packet should be handled.
	vals = s.providerApp.GetTestStakingKeeper().GetAllValidators(s.providerCtx())
	s.Require().True(vals[1].IsJailed())
	s.Require().Equal(int64(0),
		s.providerApp.GetTestStakingKeeper().GetLastValidatorPower(s.providerCtx(), vals[1].GetOperator()))

	// Now slash meter should be negative
	s.Require().True(s.providerApp.GetProviderKeeper().GetSlashMeter(s.providerCtx()).IsNegative())

	// Send another slash packet for different val
	tmval2 := s.providerChain.Vals.Validators[2]
	packet2 := s.constructSlashPacketFromConsumer(s.getFirstBundle(), *tmval2, stakingtypes.Infraction_INFRACTION_DOWNTIME, 1)
	sendOnConsumerRecvOnProvider(s, s.getFirstBundle().Path, packet2)

	// TODO: assert a bounce ack, and have these be applied back on consumer. Go through the order of how shit would happen

	// Val shouldn't be jailed
	s.Require().False(vals[2].IsJailed())
	s.Require().Equal(int64(1000),
		providerStakingKeeper.GetLastValidatorPower(s.providerCtx(), vals[2].GetOperator()))
}
