package e2e

import (
	"time"

	sdktypes "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	icstestingutils "github.com/cosmos/interchain-security/testutil/ibc_testing"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"
	tmtypes "github.com/tendermint/tendermint/types"
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
		{"0.1", 400, -600, 300, 3}, // 600/300 = 2, so 3 replenishes to reach positive
		{"0.05", 200, -800, 150, 6},
		{"0.01", 40, -960, 30, 33}, // 960/30 = 32, so 33 replenishes to reach positive
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
		tmVal := s.providerChain.Vals.Validators[0]
		packet := s.constructSlashPacketFromConsumer(s.getFirstBundle(), *tmVal, stakingtypes.Downtime, 1)
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
		tmVal = s.providerChain.Vals.Validators[2]
		packet = s.constructSlashPacketFromConsumer(s.getFirstBundle(), *tmVal, stakingtypes.Downtime, 2)
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

			// Check that slash meter is still negative or 0,
			// unless we are on the last iteration.
			if i != tc.expectedReplenishesTillPositive-1 {
				s.Require().False(slashMeter.IsPositive())
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

// TestMultiConsumerSlashPacketThrottling tests slash packet throttling in the context of multiple
// consumers sending slash packets to the provider, with VSC matured packets sprinkled around.
func (s *CCVTestSuite) TestMultiConsumerSlashPacketThrottling() {

	// Setup test
	s.SetupTest()
	s.SetupAllCCVChannels()
	s.setupValidatorPowers()

	providerKeeper := s.providerApp.GetProviderKeeper()
	providerStakingKeeper := s.providerApp.GetE2eStakingKeeper()

	// First confirm that VSC matured packets are handled immediately (not queued)
	// when no slash packets are sent.

	// Send 2 VSC matured packets from every consumer to provider
	for consumerChainID, bundle := range s.consumerBundles {
		packet := s.constructVSCMaturedPacketFromConsumer(*bundle, 1) // use sequence 1
		sendOnConsumerRecvOnProvider(s, bundle.Path, packet)
		packet = s.constructVSCMaturedPacketFromConsumer(*bundle, 2) // use sequence 2
		sendOnConsumerRecvOnProvider(s, bundle.Path, packet)
		// Confirm packets were not queued on provider for this consumer
		s.Require().Equal(uint64(0),
			providerKeeper.GetPendingPacketDataSize(s.providerCtx(), consumerChainID))
	}

	// Choose 3 consumer bundles. It doesn't matter which ones.
	idx := 0
	senderBundles := []*icstestingutils.ConsumerBundle{}
	for _, bundle := range s.consumerBundles {
		if idx > 2 {
			break
		}
		senderBundles = append(senderBundles, bundle)
		idx++
	}

	// Send some packets to provider from the 3 chosen consumers.
	// They will each slash a different validator according to idx.
	idx = 0
	valsToSlash := []tmtypes.Validator{}
	for _, bundle := range senderBundles {

		// Alternate between downtime and double sign infractions
		downtime := idx%2 == 0
		var infractionType stakingtypes.InfractionType
		if downtime {
			infractionType = stakingtypes.Downtime
		} else {
			infractionType = stakingtypes.DoubleSign
		}

		// Setup signing info for validator to be jailed
		s.setDefaultValSigningInfo(*s.providerChain.Vals.Validators[idx])

		// Send slash packet from consumer to provider

		tmVal := s.providerChain.Vals.Validators[idx]
		valsToSlash = append(valsToSlash, *tmVal)
		packet := s.constructSlashPacketFromConsumer(
			*bundle,
			*tmVal,
			infractionType,
			3, // use sequence 3, 1 and 2 are used above.
		)
		sendOnConsumerRecvOnProvider(s, bundle.Path, packet)

		// Send two trailing VSC matured packets from consumer to provider
		packet = s.constructVSCMaturedPacketFromConsumer(*bundle, 4) // use sequence 4
		sendOnConsumerRecvOnProvider(s, bundle.Path, packet)
		packet = s.constructVSCMaturedPacketFromConsumer(*bundle, 5) // use sequence 5
		sendOnConsumerRecvOnProvider(s, bundle.Path, packet)

		idx++
	}

	// Confirm that the slash packet and trailing VSC matured packet
	// were handled immediately for the first consumer (this packet was recv first).
	s.confirmValidatorJailed(valsToSlash[0], true)
	s.Require().Equal(uint64(0), providerKeeper.GetPendingPacketDataSize(
		s.providerCtx(), senderBundles[0].Chain.ChainID))

	// Packets were queued for the second and third consumers.
	s.confirmValidatorNotJailed(valsToSlash[1], 1000)
	s.Require().Equal(uint64(3), providerKeeper.GetPendingPacketDataSize(
		s.providerCtx(), senderBundles[1].Chain.ChainID))
	s.confirmValidatorNotJailed(valsToSlash[2], 1000)
	s.Require().Equal(uint64(3), providerKeeper.GetPendingPacketDataSize(
		s.providerCtx(), senderBundles[2].Chain.ChainID))

	// Total power is now 3000
	s.Require().Equal(int64(3000),
		providerStakingKeeper.GetLastTotalPower(s.providerCtx()).Int64())

	// Now replenish the slash meter and confirm one of two queued slash
	// packet entries are then handled. Order is irrelevant here since those
	// two packets were sent and recv at the same block time when being queued.
	s.replenishSlashMeterTillPositive()

	// 1st NextBlock will handle the slash packet, 2nd will update staking module val powers
	s.providerChain.NextBlock()
	s.providerChain.NextBlock()

	// If one of the entires was handled, total power will be 2000 (1000 power was slashed)
	s.Require().Equal(int64(2000),
		providerStakingKeeper.GetLastTotalPower(s.providerCtx()).Int64())

	// Now replenish one more time, and handle final slash packet.
	s.replenishSlashMeterTillPositive()

	// 1st NextBlock will handle the slash packet, 2nd will update last validator power
	s.providerChain.NextBlock()
	s.providerChain.NextBlock()

	// Total power is now 1000 (just a single validator left)
	s.Require().Equal(int64(1000),
		providerStakingKeeper.GetLastTotalPower(s.providerCtx()).Int64())

	// Now all 3 expected vals are jailed, and there are no more queued
	// slash/vsc matured packets.
	for _, val := range valsToSlash {
		s.confirmValidatorJailed(val, true)
	}
	s.Require().Equal(uint64(0), providerKeeper.GetPendingPacketDataSize(
		s.providerCtx(), senderBundles[0].Chain.ChainID))
	s.Require().Equal(uint64(0), providerKeeper.GetPendingPacketDataSize(
		s.providerCtx(), senderBundles[1].Chain.ChainID))
	s.Require().Equal(uint64(0), providerKeeper.GetPendingPacketDataSize(
		s.providerCtx(), senderBundles[2].Chain.ChainID))

	// All global queue entries are gone too
	s.Require().Empty(providerKeeper.GetAllPendingSlashPacketEntries(s.providerCtx()))
}

// TestSlashingSmallValidators tests that multiple slash packets from validators with small
// power can be handled by the provider chain in a non-throttled manner.
func (s *CCVTestSuite) TestSlashingSmallValidators() {

	s.SetupAllCCVChannels()

	// Setup first val with 1000 power and the rest with 10 power.
	delAddr := s.providerChain.SenderAccount.GetAddress()
	delegateByIdx(s, delAddr, sdktypes.NewInt(999999999), 0)
	delegateByIdx(s, delAddr, sdktypes.NewInt(9999999), 1)
	delegateByIdx(s, delAddr, sdktypes.NewInt(9999999), 2)
	delegateByIdx(s, delAddr, sdktypes.NewInt(9999999), 3)
	s.providerChain.NextBlock()

	// Replenish slash meter with default params and new total voting power.
	customCtx := s.getCtxWithReplenishPeriodElapsed(s.providerCtx())
	s.providerApp.GetProviderKeeper().CheckForSlashMeterReplenishment(customCtx)

	// Assert that we start out with no jailings
	providerStakingKeeper := s.providerApp.GetE2eStakingKeeper()
	vals := providerStakingKeeper.GetAllValidators(s.providerCtx())
	for _, val := range vals {
		s.Require().False(val.IsJailed())
	}

	// Setup signing info for jailings
	s.setDefaultValSigningInfo(*s.providerChain.Vals.Validators[1])
	s.setDefaultValSigningInfo(*s.providerChain.Vals.Validators[2])
	s.setDefaultValSigningInfo(*s.providerChain.Vals.Validators[3])

	// Send slash packets from consumer to provider for small validators.
	tmval1 := s.providerChain.Vals.Validators[1]
	tmval2 := s.providerChain.Vals.Validators[2]
	tmval3 := s.providerChain.Vals.Validators[3]
	packet1 := s.constructSlashPacketFromConsumer(s.getFirstBundle(), *tmval1, stakingtypes.DoubleSign, 1)
	packet2 := s.constructSlashPacketFromConsumer(s.getFirstBundle(), *tmval2, stakingtypes.Downtime, 2)
	packet3 := s.constructSlashPacketFromConsumer(s.getFirstBundle(), *tmval3, stakingtypes.Downtime, 3)
	sendOnConsumerRecvOnProvider(s, s.getFirstBundle().Path, packet1)
	sendOnConsumerRecvOnProvider(s, s.getFirstBundle().Path, packet2)
	sendOnConsumerRecvOnProvider(s, s.getFirstBundle().Path, packet3)

	// Default slash meter replenish fraction is 0.05, so all sent packets should be handled immediately.
	vals = providerStakingKeeper.GetAllValidators(s.providerCtx())
	s.Require().False(vals[0].IsJailed())
	s.Require().Equal(int64(1000),
		providerStakingKeeper.GetLastValidatorPower(s.providerCtx(), vals[0].GetOperator()))
	s.Require().True(vals[1].IsJailed())
	s.Require().Equal(int64(0),
		providerStakingKeeper.GetLastValidatorPower(s.providerCtx(), vals[1].GetOperator()))
	s.Require().True(vals[2].IsJailed())
	s.Require().Equal(int64(0),
		providerStakingKeeper.GetLastValidatorPower(s.providerCtx(), vals[2].GetOperator()))
	s.Require().True(vals[3].IsJailed())
	s.Require().Equal(int64(0),
		providerStakingKeeper.GetLastValidatorPower(s.providerCtx(), vals[3].GetOperator()))
}

// TestSlashMeterAllowanceChanges tests scenarios where the slash meter allowance is expected to change.
func (s *CCVTestSuite) TestSlashMeterAllowanceChanges() {
	s.SetupAllCCVChannels()

	providerKeeper := s.providerApp.GetProviderKeeper()

	// At first, allowance is based on 4 vals all with 1 power, min allowance is in effect.
	s.Require().Equal(int64(1), providerKeeper.GetSlashMeterAllowance(s.providerCtx()).Int64())

	s.setupValidatorPowers()

	// Now all 4 validators have 1000 power (4000 total power) so allowance should be:
	// default replenish frac * 4000 = 200
	s.Require().Equal(int64(200), providerKeeper.GetSlashMeterAllowance(s.providerCtx()).Int64())

	// Now we change replenish fraction and assert new expected allowance.
	params := providerKeeper.GetParams(s.providerCtx())
	params.SlashMeterReplenishFraction = "0.3"
	providerKeeper.SetParams(s.providerCtx(), params)
	s.Require().Equal(int64(1200), providerKeeper.GetSlashMeterAllowance(s.providerCtx()).Int64())

}

// TestSlashSameValidator tests the edge case that that the total slashed validator power
// queued up for a single block exceeds the slash meter allowance,
// but some of the slash packets are for the same validator, and therefore some packets
// will be applied to a validator that is already jailed but still not unbonded (ie. still slashable).
func (s *CCVTestSuite) TestSlashSameValidator() {

	s.SetupAllCCVChannels()

	// Setup 4 validators with 25% of the total power each.
	s.setupValidatorPowers()

	providerKeeper := s.providerApp.GetProviderKeeper()

	// Set replenish fraction to 1.0 so that all sent packets should handled immediately (no throttling)
	params := providerKeeper.GetParams(s.providerCtx())
	params.SlashMeterReplenishFraction = "1.0"
	providerKeeper.SetParams(s.providerCtx(), params)
	providerKeeper.InitializeSlashMeter(s.providerCtx())

	// Send a downtime and double-sign slash packet for 3/4 validators
	// This will have a total slashing power of 150% total power.
	tmval1 := s.providerChain.Vals.Validators[1]
	tmval2 := s.providerChain.Vals.Validators[2]
	tmval3 := s.providerChain.Vals.Validators[3]
	s.setDefaultValSigningInfo(*tmval1)
	s.setDefaultValSigningInfo(*tmval2)
	s.setDefaultValSigningInfo(*tmval3)

	packets := []channeltypes.Packet{
		s.constructSlashPacketFromConsumer(s.getFirstBundle(), *tmval1, stakingtypes.Downtime, 1),
		s.constructSlashPacketFromConsumer(s.getFirstBundle(), *tmval2, stakingtypes.Downtime, 2),
		s.constructSlashPacketFromConsumer(s.getFirstBundle(), *tmval3, stakingtypes.Downtime, 3),
		s.constructSlashPacketFromConsumer(s.getFirstBundle(), *tmval1, stakingtypes.DoubleSign, 4),
		s.constructSlashPacketFromConsumer(s.getFirstBundle(), *tmval2, stakingtypes.DoubleSign, 5),
		s.constructSlashPacketFromConsumer(s.getFirstBundle(), *tmval3, stakingtypes.DoubleSign, 6),
	}

	// Recv and queue all slash packets.
	for _, packet := range packets {
		slashPacketData := ccvtypes.SlashPacketData{}
		ccvtypes.ModuleCdc.MustUnmarshalJSON(packet.GetData(), &slashPacketData)
		providerKeeper.OnRecvSlashPacket(s.providerCtx(), packet, slashPacketData)
	}

	// We should have 6 pending slash packet entries queued.
	s.Require().Len(providerKeeper.GetAllPendingSlashPacketEntries(s.providerCtx()), 6)

	// Call next block to process all pending slash packets in end blocker.
	s.providerChain.NextBlock()

	// All slash packets should have been handled immediately, even though they totaled to 150% of total power.
	s.Require().Len(providerKeeper.GetAllPendingSlashPacketEntries(s.providerCtx()), 0)
}

// Similar to TestSlashSameValidator, but 100% of val power is jailed a single block,
// and in the first packets recv for that block.
// This edge case should not occur in practice, but is useful to validate that
// the slash meter can allow any number of slash packets to be handled in a single block when
// its allowance is set to "1.0".
func (s CCVTestSuite) TestSlashAllValidators() {

	s.SetupAllCCVChannels()

	// Setup 4 validators with 25% of the total power each.
	s.setupValidatorPowers()

	providerKeeper := s.providerApp.GetProviderKeeper()

	// Set replenish fraction to 1.0 so that all sent packets should be handled immediately (no throttling)
	params := providerKeeper.GetParams(s.providerCtx())
	params.SlashMeterReplenishFraction = "1.0"
	providerKeeper.SetParams(s.providerCtx(), params)
	providerKeeper.InitializeSlashMeter(s.providerCtx())

	// The packets to be recv in a single block, ordered as they will be recv.
	packets := []channeltypes.Packet{}

	// Track and increment ibc seq num for each packet, since these need to be unique.
	ibcSeqNum := uint64(1)

	// Instantiate a slash packet for each validator,
	// these first 4 packets should jail 100% of the total power.
	for _, val := range s.providerChain.Vals.Validators {
		s.setDefaultValSigningInfo(*val)
		packets = append(packets, s.constructSlashPacketFromConsumer(
			s.getFirstBundle(), *val, stakingtypes.Downtime, ibcSeqNum))
		ibcSeqNum++
	}

	// add 5 more slash packets for each validator, that will be handled in the same block.
	for idx, val := range s.providerChain.Vals.Validators {
		// Set infraction type based on even/odd index.
		var infractionType stakingtypes.InfractionType
		if idx%2 == 0 {
			infractionType = stakingtypes.Downtime
		} else {
			infractionType = stakingtypes.DoubleSign
		}
		for i := 0; i < 5; i++ {
			packets = append(packets, s.constructSlashPacketFromConsumer(
				s.getFirstBundle(), *val, infractionType, ibcSeqNum))
			ibcSeqNum++
		}
	}

	// Recv and queue all slash packets.
	for _, packet := range packets {
		slashPacketData := ccvtypes.SlashPacketData{}
		ccvtypes.ModuleCdc.MustUnmarshalJSON(packet.GetData(), &slashPacketData)
		providerKeeper.OnRecvSlashPacket(s.providerCtx(), packet, slashPacketData)
	}

	// We should have 24 pending slash packet entries queued.
	s.Require().Len(providerKeeper.GetAllPendingSlashPacketEntries(s.providerCtx()), 24)

	// Call next block to process all pending slash packets in end blocker.
	s.providerChain.NextBlock()

	// All slash packets should have been handled immediately,
	// even though the first 4 packets jailed 100% of the total power.
	s.Require().Len(providerKeeper.GetAllPendingSlashPacketEntries(s.providerCtx()), 0)

	// Sanity check that all validators are jailed.
	for _, val := range s.providerChain.Vals.Validators {
		// Do not check power, since val power is not yet updated by staking endblocker.
		s.confirmValidatorJailed(*val, false)
	}

	// Nextblock would fail the test now, since ibctesting fails when
	// "applying the validator changes would result in empty set".
}

func (s *CCVTestSuite) confirmValidatorJailed(tmVal tmtypes.Validator, checkPower bool) {
	sdkVal, found := s.providerApp.GetE2eStakingKeeper().GetValidator(
		s.providerCtx(), sdktypes.ValAddress(tmVal.Address))
	s.Require().True(found)
	s.Require().True(sdkVal.IsJailed())

	if checkPower {
		valPower := s.providerApp.GetE2eStakingKeeper().GetLastValidatorPower(
			s.providerCtx(), sdkVal.GetOperator())
		s.Require().Equal(int64(0), valPower)
	}
}

func (s *CCVTestSuite) confirmValidatorNotJailed(tmVal tmtypes.Validator, expectedPower int64) {
	sdkVal, found := s.providerApp.GetE2eStakingKeeper().GetValidator(
		s.providerCtx(), sdktypes.ValAddress(tmVal.Address))
	s.Require().True(found)
	valPower := s.providerApp.GetE2eStakingKeeper().GetLastValidatorPower(
		s.providerCtx(), sdkVal.GetOperator())
	s.Require().Equal(expectedPower, valPower)
	s.Require().False(sdkVal.IsJailed())
}

func (s *CCVTestSuite) replenishSlashMeterTillPositive() {
	providerKeeper := s.providerApp.GetProviderKeeper()
	idx := 0
	for providerKeeper.GetSlashMeter(s.providerCtx()).IsNegative() {
		if idx > 100 {
			panic("replenishTillPositive: failed to replenish slash meter")
		}
		providerKeeper.ReplenishSlashMeter(s.providerCtx())
	}
}

func (s *CCVTestSuite) getCtxWithReplenishPeriodElapsed(ctx sdktypes.Context) sdktypes.Context {

	providerKeeper := s.providerApp.GetProviderKeeper()
	lastFullTime := providerKeeper.GetLastSlashMeterFullTime(ctx)
	replenishPeriod := providerKeeper.GetSlashMeterReplenishPeriod(ctx)

	return ctx.WithBlockTime(lastFullTime.Add(replenishPeriod).Add(time.Minute))
}
