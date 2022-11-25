package e2e

import (
	"time"

	sdktypes "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
)

// TestBasicSlashPacketThrottling tests slash packet throttling with a single consumer,
// two slash packets, and no VSC matured packets. The most basic scenario.
func (s *CCVTestSuite) TestBasicSlashPacketThrottling() {

	// setupValidatePowers gives the default 4 validators 25% power each (1000 power).
	// Note this in test cases.
	testCases := []struct {
		replenishFraction                string
		expectedMeterBeforeFirstSlash    int64
		expectedMeterAfterFirstSlash     int64
		expectedAllowanceAfterFirstSlash int64
		expectedReplenishesTillPositive  int
	}{
		{"0.2", 800, -200, 600, 1},
	}

	for _, tc := range testCases {

		s.SetupTest()
		s.SetupAllCCVChannels()
		s.setupValidatorPowers()

		providerStakingKeeper := s.providerApp.GetE2eStakingKeeper()

		// Use default params (incl replenish period), but set replenish fraction to tc value.
		params := providertypes.DefaultParams()
		params.SlashMeterReplenishFraction = tc.replenishFraction
		s.providerApp.GetProviderKeeper().SetParams(s.providerCtx(), params)

		// Elapse a replenish period and check for replenishment, so new param is fully in effect.
		customCtx := s.getCtxWithReplenishPeriodElapsed(s.providerCtx())
		s.providerApp.GetProviderKeeper().CheckForSlashMeterReplenishment(customCtx)

		slashMeter := s.providerApp.GetProviderKeeper().GetSlashMeter(s.providerCtx())
		s.Require().Equal(tc.expectedMeterBeforeFirstSlash, slashMeter.Int64())

		// Assert that we start out with no jailings
		vals := providerStakingKeeper.GetAllValidators(s.providerCtx())
		for _, val := range vals {
			s.Require().False(val.IsJailed())
		}

		// Send a slash packet from consumer to provider
		s.setDefaultValSigningInfo(*s.providerChain.Vals.Validators[0])
		packet := s.constructSlashPacketFromConsumer(s.getFirstBundle(), 0, stakingtypes.Downtime, 1)
		sendOnConsumerRecvOnProvider(s, s.getFirstBundle().Path, packet)

		// Assert validator 0 is jailed and has no power
		vals = providerStakingKeeper.GetAllValidators(s.providerCtx())
		slashedVal := vals[0]
		s.Require().True(slashedVal.IsJailed())
		lastValPower := providerStakingKeeper.GetLastValidatorPower(s.providerCtx(), slashedVal.GetOperator())
		s.Require().Equal(int64(0), lastValPower)

		// Assert expected slash meter and allowance value
		slashMeter = s.providerApp.GetProviderKeeper().GetSlashMeter(s.providerCtx())
		s.Require().Equal(tc.expectedMeterAfterFirstSlash, slashMeter.Int64())
		s.Require().Equal(tc.expectedAllowanceAfterFirstSlash,
			s.providerApp.GetProviderKeeper().GetSlashMeterAllowance(s.providerCtx()).Int64())

		// Now send a second slash packet from consumer to provider for a different validator.
		s.setDefaultValSigningInfo(*s.providerChain.Vals.Validators[2])
		packet = s.constructSlashPacketFromConsumer(s.getFirstBundle(), 2, stakingtypes.Downtime, 2)
		sendOnConsumerRecvOnProvider(s, s.getFirstBundle().Path, packet)

		// Require that slash packet has not been handled
		vals = providerStakingKeeper.GetAllValidators(s.providerCtx())
		s.Require().False(vals[2].IsJailed())

		// Assert slash meter value is still the same
		slashMeter = s.providerApp.GetProviderKeeper().GetSlashMeter(s.providerCtx())
		s.Require().Equal(tc.expectedMeterAfterFirstSlash, slashMeter.Int64())

		// Replenish slash meter until it is positive
		for i := 0; i < tc.expectedReplenishesTillPositive; i++ {

			// Mutate context with a block time where replenish period has passed.
			customCtx = s.getCtxWithReplenishPeriodElapsed(s.providerCtx())

			// CheckForSlashMeterReplenishment should replenish meter here.
			slashMeterBefore := s.providerApp.GetProviderKeeper().GetSlashMeter(s.providerCtx())
			s.providerApp.GetProviderKeeper().CheckForSlashMeterReplenishment(customCtx)
			slashMeter = s.providerApp.GetProviderKeeper().GetSlashMeter(s.providerCtx())
			s.Require().True(slashMeter.GT(slashMeterBefore))

			// Check that slash meter is still negative, unless we are on the last iteration.
			if i != tc.expectedReplenishesTillPositive-1 {
				s.Require().True(slashMeter.IsNegative())
			}
		}

		// Meter is positive at this point, and ready to handle the second slash packet.
		slashMeter = s.providerApp.GetProviderKeeper().GetSlashMeter(s.providerCtx())
		s.Require().True(slashMeter.IsPositive())

		// Assert validator 2 is jailed once pending slash packets are handled in ccv endblocker.
		s.providerChain.NextBlock()
		vals = providerStakingKeeper.GetAllValidators(s.providerCtx())
		slashedVal = vals[2]
		s.Require().True(slashedVal.IsJailed())

		// Assert validator 2 has no power, this should be apparent next block,
		// since the staking endblocker runs before the ccv endblocker.
		s.providerChain.NextBlock()
		lastValPower = providerStakingKeeper.GetLastValidatorPower(s.providerCtx(), slashedVal.GetOperator())
		s.Require().Equal(int64(0), lastValPower)
	}
}

func (s *CCVTestSuite) getCtxWithReplenishPeriodElapsed(ctx sdktypes.Context) sdktypes.Context {

	providerKeeper := s.providerApp.GetProviderKeeper()
	lastReplenishTime := providerKeeper.GetLastSlashMeterReplenishTime(ctx)
	replenishPeriod := providerKeeper.GetSlashMeterReplenishPeriod(ctx)

	return ctx.WithBlockTime(lastReplenishTime.Add(replenishPeriod).Add(time.Minute))
}

// TODO: test replenishment logic on it's own test (change ctx time)

// TODO: test logic of param being changed.

// TODO: logic on meter being full?

// TODO: assert more logic about meter level, etc.

// TODO(Shawn): Add more e2e tests for edge cases

// TODO: write test around replenish fraction being too small and the allowance being 1 (min value)

// TODO: test vsc matured stuff too, or add to above test?

// TODO: multiple consumers

// TODO: Move to common.go and use in other slashing tests that you copied this from
