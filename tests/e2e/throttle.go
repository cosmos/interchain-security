package e2e

import (
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
)

func (s *CCVTestSuite) TestSlashPacketThrottling() {
	s.SetupAllCCVChannels()
	s.setupValidatorPowers()

	// try different params in test cases
	params := providertypes.DefaultParams()
	params.SlashMeterReplenishFraction = "0.2" // Will take two replenishes for second slash
	s.providerApp.GetProviderKeeper().SetParams(s.providerCtx(), params)

	valsBefore := s.getValidatorsWithPower()
	s.setDefaultValSigningInfo(*s.providerChain.Vals.Validators[0])
	packet := s.constructSlashPacketFromConsumer(s.getFirstBundle(), 0, stakingtypes.Downtime, 1)

	sendOnConsumerRecvOnProvider(s, s.getFirstBundle().Path, packet)
	s.providerChain.NextBlock() // cause N+3, TODO: needed?

	valsAfter := s.getValidatorsWithPower()

	s.Require().Equal(len(valsBefore)-1, len(valsAfter))
	slashMeter := s.providerApp.GetProviderKeeper().GetSlashMeter(s.providerCtx())
	s.Require().True(slashMeter.IsNegative())

	s.setDefaultValSigningInfo(*s.providerChain.Vals.Validators[2])
	packet = s.constructSlashPacketFromConsumer(s.getFirstBundle(), 2, stakingtypes.Downtime, 2)

	sendOnConsumerRecvOnProvider(s, s.getFirstBundle().Path, packet)
	s.providerChain.NextBlock() // cause N+3

	// Val isn't removed yet, slash meter is negative
	s.Require().Equal(len(valsAfter), len(s.getValidatorsWithPower()))
	s.Require().True(slashMeter.IsNegative())

	// TODO: do the below better, maybe replenish through block time.
	s.providerApp.GetProviderKeeper().ReplenishSlashMeter(s.providerCtx())
	slashMeter = s.providerApp.GetProviderKeeper().GetSlashMeter(s.providerCtx())
	s.Require().True(slashMeter.IsNegative())
	s.providerApp.GetProviderKeeper().ReplenishSlashMeter(s.providerCtx())
	slashMeter = s.providerApp.GetProviderKeeper().GetSlashMeter(s.providerCtx())
	s.Require().True(slashMeter.IsPositive())

	// TODO: assert more logic about meter level, etc.

	s.providerChain.NextBlock()
	s.providerChain.NextBlock()
	s.providerChain.NextBlock()

	// Val is removed
	s.Require().Equal(len(valsBefore)-2, len(s.getValidatorsWithPower()))

}

// TODO(Shawn): Add more e2e tests for edge cases

// TODO: write test around replenish fraction being too small and the allowance being 1 (min value)

// TODO: test vsc matured stuff too, or add to above test?

// TODO: multiple consumers

// TODO: Move to common.go and use in other slashing tests that you copied this from
