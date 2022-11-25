package e2e

import (
	"time"

	sdktypes "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
)

func (s *CCVTestSuite) TestBasicSlashPacketThrottling() {
	s.SetupAllCCVChannels()
	s.setupValidatorPowers()

	// try different params in test cases
	params := providertypes.DefaultParams()
	params.SlashMeterReplenishFraction = "0.2" // Will take two replenishes for second slash
	providerKeeper := s.providerApp.GetProviderKeeper()
	providerKeeper.SetParams(s.providerCtx(), params)

	valsBefore := s.getValidatorsWithPower()

	// Send a slash packet from consumer to provider
	s.setDefaultValSigningInfo(*s.providerChain.Vals.Validators[0])
	packet := s.constructSlashPacketFromConsumer(s.getFirstBundle(), 0, stakingtypes.Downtime, 1)
	sendOnConsumerRecvOnProvider(s, s.getFirstBundle().Path, packet)
	// Two blocks pass by from above function. We need one more block to pass before val powers are updated.
	// See TestRelayAndApplySlashPacket for more in depth explanation.
	s.providerChain.NextBlock()

	valsAfter := s.getValidatorsWithPower()

	// Require that slashed validator was removed from valset, ie. slash packet was handled.
	s.Require().Equal(len(valsBefore)-1, len(valsAfter))
	slashMeter := s.providerApp.GetProviderKeeper().GetSlashMeter(s.providerCtx())

	// Slash meter is now negative
	s.Require().True(slashMeter.IsNegative())

	// Now send a second slash packet from consumer to provider.
	s.setDefaultValSigningInfo(*s.providerChain.Vals.Validators[2])
	packet = s.constructSlashPacketFromConsumer(s.getFirstBundle(), 2, stakingtypes.Downtime, 2)
	sendOnConsumerRecvOnProvider(s, s.getFirstBundle().Path, packet)
	s.providerChain.NextBlock()

	// Require that slash packet has not been handled, since val isn't removed from valset yet.
	s.Require().Equal(len(valsAfter), len(s.getValidatorsWithPower()))

	// Slash meter is still negative
	slashMeter = s.providerApp.GetProviderKeeper().GetSlashMeter(s.providerCtx())
	s.Require().True(slashMeter.IsNegative())

	// Replenish slash meter by instantiating a context with a block time where replenish period has passed.
	ctx := s.getCtxWithReplenishPeriodElapsed(s.providerCtx())

	// CheckForSlashMeterReplenishment should replenish meter here. But it'll still be negative.
	slashMeterBefore := providerKeeper.GetSlashMeter(ctx)
	providerKeeper.CheckForSlashMeterReplenishment(ctx)
	slashMeter = providerKeeper.GetSlashMeter(s.providerCtx())
	s.Require().Greater(slashMeter.Int64(), slashMeterBefore.Int64())
	s.Require().True(slashMeter.IsNegative())

	// Elapse another replenish period.
	ctx = s.getCtxWithReplenishPeriodElapsed(ctx)

	// CheckForSlashMeterReplenishment should replenish meter here. Meter should now be positive.
	slashMeterBefore = providerKeeper.GetSlashMeter(ctx)
	providerKeeper.CheckForSlashMeterReplenishment(ctx)
	slashMeter = providerKeeper.GetSlashMeter(s.providerCtx())
	s.Require().Greater(slashMeter.Int64(), slashMeterBefore.Int64())
	s.Require().True(slashMeter.IsPositive())

	// Advance 3 blocks to commit new valset where the second slash packet is handled
	s.providerChain.NextBlock()
	s.providerChain.NextBlock()
	s.providerChain.NextBlock()

	// Assert val is removed
	s.Require().Equal(len(valsBefore)-2, len(s.getValidatorsWithPower()))
}

func (s *CCVTestSuite) getCtxWithReplenishPeriodElapsed(ctx sdktypes.Context) sdktypes.Context {

	providerKeeper := s.providerApp.GetProviderKeeper()
	lastReplenishTime := providerKeeper.GetLastSlashMeterReplenishTime(ctx)
	replenishPeriod := providerKeeper.GetSlashMeterReplenishPeriod(ctx)

	return ctx.WithBlockTime(lastReplenishTime.Add(replenishPeriod).Add(time.Minute))
}

// TODO: assert more logic about meter level, etc.

// TODO(Shawn): Add more e2e tests for edge cases

// TODO: write test around replenish fraction being too small and the allowance being 1 (min value)

// TODO: test vsc matured stuff too, or add to above test?

// TODO: multiple consumers

// TODO: Move to common.go and use in other slashing tests that you copied this from
