package integration

import (
	"time"

	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	tmtypes "github.com/cometbft/cometbft/types"

	icstestingutils "github.com/cosmos/interchain-security/v4/testutil/ibc_testing"
	"github.com/cosmos/interchain-security/v4/x/ccv/provider"
	providertypes "github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v4/x/ccv/types"
)

const fullSlashMeterString = "1.0"

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
		{
			"0.2",
			800,  // replenishFraction * totalPower: 0.2 * 4000
			-200, // expectedMeterBeforeFirstSlash - power(V0): 800 - 1000
			600,  // replenishFraction * newTotalPower: 0.2 * 3000
			1,    // ceil((200+1)/600)
		},
		{
			"0.1",
			400,  // replenishFraction * totalPower: 0.1 * 4000
			-600, // expectedMeterBeforeFirstSlash - power(V0): 400 - 1000
			300,  // replenishFraction * newTotalPower: 0.1 * 3000
			3,    // ceil((600+1)/300)
		},
		{
			"0.05",
			200,  // replenishFraction * totalPower: 0.05 * 4000
			-800, // expectedMeterBeforeFirstSlash - power(V0): 200 - 1000
			150,  // replenishFraction * newTotalPower: 0.05 * 3000
			6,    // ceil((800+1)/150)
		},
		{
			"0.01",
			40,   // replenishFraction * totalPower: 0.01 * 4000
			-960, // expectedMeterBeforeFirstSlash - power(V0): 40 - 1000
			30,   // replenishFraction * newTotalPower: 0.01 * 3000
			33,   // ceil((960+1)/30)
		},
	}

	for _, tc := range testCases {

		s.SetupTest()
		s.SetupAllCCVChannels()
		s.setupValidatorPowers([]int64{1000, 1000, 1000, 1000})

		providerStakingKeeper := s.providerApp.GetTestStakingKeeper()

		// Use default params (incl replenish period), but set replenish fraction to tc value.
		params := providertypes.DefaultParams()
		params.SlashMeterReplenishFraction = tc.replenishFraction
		s.providerApp.GetProviderKeeper().SetParams(s.providerCtx(), params)

		s.providerApp.GetProviderKeeper().InitializeSlashMeter(s.providerCtx())

		slashMeter := s.providerApp.GetProviderKeeper().GetSlashMeter(s.providerCtx())
		s.Require().Equal(tc.expectedMeterBeforeFirstSlash, slashMeter.Int64())

		// Assert that we start out with no jailings
		vals := providerStakingKeeper.GetAllValidators(s.providerCtx())
		for _, val := range vals {
			s.Require().False(val.IsJailed())
		}
		var (
			timeoutHeight    = clienttypes.Height{}
			timeoutTimestamp = uint64(s.getFirstBundle().GetCtx().BlockTime().Add(ccvtypes.DefaultCCVTimeoutPeriod).UnixNano())
		)

		// Send a slash packet from consumer to provider
		s.setDefaultValSigningInfo(*s.providerChain.Vals.Validators[0])
		tmVal := s.providerChain.Vals.Validators[0]
		slashPacket := s.constructSlashPacketFromConsumer(s.getFirstBundle(), *tmVal, stakingtypes.Infraction_INFRACTION_DOWNTIME, 1)
		sendOnConsumerRecvOnProvider(s, s.getFirstBundle().Path, timeoutHeight, timeoutTimestamp, slashPacket.GetData())

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
		slashPacket = s.constructSlashPacketFromConsumer(s.getFirstBundle(), *tmVal, stakingtypes.Infraction_INFRACTION_DOWNTIME, 2)
		sendOnConsumerRecvOnProvider(s, s.getFirstBundle().Path, timeoutHeight, timeoutTimestamp, slashPacket.GetData())

		// Require that slash packet has not been handled, a bounce result would have
		// been returned, but the IBC helper throws out acks.
		vals = providerStakingKeeper.GetAllValidators(s.providerCtx())
		s.Require().False(vals[2].IsJailed())

		// Assert slash meter value is still the same
		slashMeter = s.providerApp.GetProviderKeeper().GetSlashMeter(s.providerCtx())
		s.Require().Equal(tc.expectedMeterAfterFirstSlash, slashMeter.Int64())

		// For the remainder of this test we use a cached context in which we can mutate block time
		cacheCtx := s.providerCtx()

		// Replenish slash meter until it is positive
		for i := 0; i < tc.expectedReplenishesTillPositive; i++ {

			// Mutate cached context to have a block time after the current replenish candidate time.
			cacheCtx = s.getCtxAfterReplenishCandidate(cacheCtx)
			candidate := s.providerApp.GetProviderKeeper().GetSlashMeterReplenishTimeCandidate(cacheCtx)
			s.Require().True(cacheCtx.BlockTime().After(candidate))

			// CheckForSlashMeterReplenishment should replenish meter here.
			slashMeterBefore := s.providerApp.GetProviderKeeper().GetSlashMeter(cacheCtx)
			s.providerApp.GetProviderKeeper().CheckForSlashMeterReplenishment(cacheCtx)
			slashMeter = s.providerApp.GetProviderKeeper().GetSlashMeter(cacheCtx)
			s.Require().True(slashMeter.GT(slashMeterBefore))

			// Replenish candidate time should have been updated to be block time + replenish period.
			expected := cacheCtx.BlockTime().Add(params.SlashMeterReplenishPeriod)
			actual := s.providerApp.GetProviderKeeper().GetSlashMeterReplenishTimeCandidate(cacheCtx)
			s.Require().Equal(expected, actual)

			// CheckForSlashMeterReplenishment should not replenish meter here again (w/o another period elapsed).
			// Replenish candidate should be in the future, and will not change.
			candidate = s.providerApp.GetProviderKeeper().GetSlashMeterReplenishTimeCandidate(cacheCtx)
			s.Require().True(cacheCtx.BlockTime().Before(candidate))
			slashMeterBefore = s.providerApp.GetProviderKeeper().GetSlashMeter(cacheCtx)
			s.providerApp.GetProviderKeeper().CheckForSlashMeterReplenishment(cacheCtx)
			s.Require().Equal(slashMeterBefore, s.providerApp.GetProviderKeeper().GetSlashMeter(cacheCtx))
			s.Require().Equal(candidate, s.providerApp.GetProviderKeeper().GetSlashMeterReplenishTimeCandidate(cacheCtx))

			// Check that slash meter is still negative or 0, unless we are on the last iteration.
			slashMeter = s.providerApp.GetProviderKeeper().GetSlashMeter(cacheCtx)
			if i != tc.expectedReplenishesTillPositive-1 {
				s.Require().False(slashMeter.IsPositive())
			}
		}

		// Meter is positive at this point, and ready to handle the second slash packet.
		slashMeter = s.providerApp.GetProviderKeeper().GetSlashMeter(cacheCtx)
		s.Require().True(slashMeter.IsPositive())

		// Assert validator 2 is jailed once slash packet is retried.
		tmVal2 := s.providerChain.Vals.Validators[2]
		packet := s.constructSlashPacketFromConsumer(s.getFirstBundle(),
			*tmVal2, stakingtypes.Infraction_INFRACTION_DOWNTIME, 3) // make sure to use a new seq num
		sendOnConsumerRecvOnProvider(s, s.getFirstBundle().Path, timeoutHeight, timeoutTimestamp, packet.GetData())

		stakingVal2 := s.mustGetStakingValFromTmVal(*tmVal2)
		s.Require().True(stakingVal2.IsJailed())

		// Assert validator 2 has no power, this should be apparent next block,
		// since the staking endblocker runs before the ccv endblocker.
		s.providerChain.NextBlock()
		lastValPower = providerStakingKeeper.GetLastValidatorPower(cacheCtx, slashedVal.GetOperator())
		s.Require().Equal(int64(0), lastValPower)
	}
}

// TestMultiConsumerSlashPacketThrottling tests slash packet throttling in the context of multiple
// consumers sending slash packets to the provider, with VSC matured packets sprinkled around.
func (s *CCVTestSuite) TestMultiConsumerSlashPacketThrottling() {
	// Setup test
	s.SetupAllCCVChannels()
	s.setupValidatorPowers([]int64{1000, 1000, 1000, 1000})

	var (
		timeoutHeight    = clienttypes.Height{}
		timeoutTimestamp = uint64(s.getFirstBundle().GetCtx().BlockTime().Add(ccvtypes.DefaultCCVTimeoutPeriod).UnixNano())
	)

	providerStakingKeeper := s.providerApp.GetTestStakingKeeper()

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

	// Send some slash packets to provider from the 3 chosen consumers.
	// They will each slash a different validator according to idx.
	idx = 0
	valsToSlash := []tmtypes.Validator{}
	for _, bundle := range senderBundles {

		// Setup signing info for validator to be jailed
		s.setDefaultValSigningInfo(*s.providerChain.Vals.Validators[idx])

		// Send downtime slash packet from consumer to provider
		tmVal := s.providerChain.Vals.Validators[idx]
		valsToSlash = append(valsToSlash, *tmVal)
		slashPacket := s.constructSlashPacketFromConsumer(
			*bundle,
			*tmVal,
			stakingtypes.Infraction_INFRACTION_DOWNTIME,
			1, // all consumers use 1 seq num
		)
		sendOnConsumerRecvOnProvider(s, bundle.Path, timeoutHeight, timeoutTimestamp, slashPacket.GetData())

		idx++
	}

	// Confirm that the slash packet for the first consumer was handled (this packet was recv first).
	s.confirmValidatorJailed(valsToSlash[0], true)

	// Packets were bounced for the second and third consumers.
	s.confirmValidatorNotJailed(valsToSlash[1], 1000) // each validator has 1000 power from the setup
	s.confirmValidatorNotJailed(valsToSlash[2], 1000)

	// Total power is now 3000 (as one validator was jailed)
	s.Require().Equal(int64(3000),
		providerStakingKeeper.GetLastTotalPower(s.providerCtx()).Int64())

	// Now replenish the slash meter and confirm one of two queued slash
	// packet entries are then handled, when both are retried.
	s.replenishSlashMeterTillPositive()

	// Retry from consumer with idx 1
	bundle := senderBundles[1]
	packet := s.constructSlashPacketFromConsumer(
		*bundle,
		valsToSlash[1],
		stakingtypes.Infraction_INFRACTION_DOWNTIME,
		2, // seq number is incremented since last try
	)
	sendOnConsumerRecvOnProvider(s, bundle.Path, timeoutHeight, timeoutTimestamp, packet.GetData())

	// retry from consumer with idx 2
	bundle = senderBundles[2]
	packet = s.constructSlashPacketFromConsumer(
		*bundle,
		valsToSlash[2],
		stakingtypes.Infraction_INFRACTION_DOWNTIME,
		2, // seq number is incremented since last try
	)
	sendOnConsumerRecvOnProvider(s, bundle.Path, timeoutHeight, timeoutTimestamp, packet.GetData())

	// Call NextBlocks to update staking module val powers
	s.providerChain.NextBlock()
	s.providerChain.NextBlock()

	// If one of the entries was handled, total power will be 2000 (1000 power was just slashed)
	s.Require().Equal(int64(2000),
		providerStakingKeeper.GetLastTotalPower(s.providerCtx()).Int64())

	// Now replenish one more time, and handle final slash packet.
	s.replenishSlashMeterTillPositive()

	// Retry from consumer with idx 2
	bundle = senderBundles[2]
	packet = s.constructSlashPacketFromConsumer(
		*bundle,
		valsToSlash[2],
		stakingtypes.Infraction_INFRACTION_DOWNTIME,
		3, // seq number is incremented since last try
	)
	sendOnConsumerRecvOnProvider(s, bundle.Path, timeoutHeight, timeoutTimestamp, packet.GetData())

	// Call NextBlocks to update staking module val powers
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
}

// TestPacketSpam confirms that the provider can handle a large number of
// incoming slash packets in a single block.
func (s *CCVTestSuite) TestPacketSpam() {
	// Setup ccv channels to all consumers
	s.SetupAllCCVChannels()

	// Setup validator powers to be 25%, 25%, 25%, 25%
	s.setupValidatorPowers([]int64{1000, 1000, 1000, 1000})

	// Explicitly set params, initialize slash meter
	providerKeeper := s.providerApp.GetProviderKeeper()
	params := providerKeeper.GetParams(s.providerCtx())
	params.SlashMeterReplenishFraction = "0.75" // Allow 3/4 of validators to be jailed
	providerKeeper.SetParams(s.providerCtx(), params)
	providerKeeper.InitializeSlashMeter(s.providerCtx())

	// The packets data to be recv in a single block, ordered as they will be recv.
	var packetsData [][]byte

	firstBundle := s.getFirstBundle()

	// Slash first 3 but not 4th validator
	s.setDefaultValSigningInfo(*s.providerChain.Vals.Validators[0])
	s.setDefaultValSigningInfo(*s.providerChain.Vals.Validators[1])
	s.setDefaultValSigningInfo(*s.providerChain.Vals.Validators[2])

	// Track and increment ibc seq num for each packet, since these need to be unique.
	ibcSeqNum := uint64(0)

	// Construct 500 slash packets
	for ibcSeqNum < 500 {
		// Increment ibc seq num for each packet (starting at 1)
		ibcSeqNum++
		// Set infraction type based on even/odd index.
		var infractionType stakingtypes.Infraction
		if ibcSeqNum%2 == 0 {
			infractionType = stakingtypes.Infraction_INFRACTION_DOWNTIME
		} else {
			infractionType = stakingtypes.Infraction_INFRACTION_DOUBLE_SIGN
		}
		valToJail := s.providerChain.Vals.Validators[ibcSeqNum%3]
		slashPacket := s.constructSlashPacketFromConsumer(firstBundle, *valToJail, infractionType, ibcSeqNum)
		packetsData = append(packetsData, slashPacket.GetData())
	}

	// Recv 500 packets from consumer to provider in same block
	var (
		timeoutHeight    = clienttypes.Height{}
		timeoutTimestamp = uint64(firstBundle.GetCtx().BlockTime().Add(ccvtypes.DefaultCCVTimeoutPeriod).UnixNano())
	)
	for sequence, data := range packetsData {
		consumerPacketData, err := provider.UnmarshalConsumerPacketData(data) // Same func used by provider's OnRecvPacket
		s.Require().NoError(err)
		packet := s.newPacketFromConsumer(data, uint64(sequence), firstBundle.Path, timeoutHeight, timeoutTimestamp)
		_, err = providerKeeper.OnRecvSlashPacket(s.providerCtx(), packet, *consumerPacketData.GetSlashPacketData())
		s.Require().NoError(err)
	}

	// Execute block
	s.providerChain.NextBlock()

	// Confirm 3 expected vals are jailed
	for i := 0; i < 3; i++ {
		val := s.providerChain.Vals.Validators[i]
		s.confirmValidatorJailed(*val, true)
	}
}

func (s *CCVTestSuite) TestDoubleSignDoesNotAffectThrottling() {
	// Setup ccv channels to all consumers
	s.SetupAllCCVChannels()

	// Setup validator powers to be 25%, 25%, 25%, 25%
	s.setupValidatorPowers([]int64{1000, 1000, 1000, 1000})

	// Explicitly set params, initialize slash meter
	providerKeeper := s.providerApp.GetProviderKeeper()
	params := providerKeeper.GetParams(s.providerCtx())
	params.SlashMeterReplenishFraction = "0.1"
	providerKeeper.SetParams(s.providerCtx(), params)
	providerKeeper.InitializeSlashMeter(s.providerCtx())

	// The packetsData to be recv in a single block, ordered as they will be recv.
	var packetsData [][]byte

	firstBundle := s.getFirstBundle()

	// Slash first 3 but not 4th validator
	s.setDefaultValSigningInfo(*s.providerChain.Vals.Validators[0])
	s.setDefaultValSigningInfo(*s.providerChain.Vals.Validators[1])
	s.setDefaultValSigningInfo(*s.providerChain.Vals.Validators[2])

	// Track and increment ibc seq num for each packet, since these need to be unique.
	ibcSeqNum := uint64(0)
	// Construct 500 double-sign slash packets
	for ibcSeqNum < 500 {
		// Increment ibc seq num for each packet (starting at 1)
		ibcSeqNum++
		valToJail := s.providerChain.Vals.Validators[ibcSeqNum%3]
		slashPacket := s.constructSlashPacketFromConsumer(firstBundle, *valToJail, stakingtypes.Infraction_INFRACTION_DOUBLE_SIGN, ibcSeqNum)
		packetsData = append(packetsData, slashPacket.GetData())
	}

	// Recv 500 packets from consumer to provider in same block
	var (
		timeoutHeight    = clienttypes.Height{}
		timeoutTimestamp = uint64(firstBundle.GetCtx().BlockTime().Add(ccvtypes.DefaultCCVTimeoutPeriod).UnixNano())
	)
	for sequence, data := range packetsData {
		consumerPacketData, err := provider.UnmarshalConsumerPacketData(data) // Same func used by provider's OnRecvPacket
		s.Require().NoError(err)
		packet := s.newPacketFromConsumer(data, uint64(sequence), firstBundle.Path, timeoutHeight, timeoutTimestamp)
		_, err = providerKeeper.OnRecvSlashPacket(s.providerCtx(), packet, *consumerPacketData.GetSlashPacketData())
		s.Require().NoError(err)
	}

	// Execute block to handle packets in endblock
	s.providerChain.NextBlock()

	// Confirm that slash meter is not affected
	s.Require().Equal(providerKeeper.GetSlashMeterAllowance(s.providerCtx()),
		providerKeeper.GetSlashMeter(s.providerCtx()))

	// Advance two blocks and confirm no validator is jailed
	s.providerChain.NextBlock()
	s.providerChain.NextBlock()

	stakingKeeper := s.providerApp.GetTestStakingKeeper()
	for _, val := range s.providerChain.Vals.Validators {
		power := stakingKeeper.GetLastValidatorPower(s.providerCtx(), sdk.ValAddress(val.Address))
		s.Require().Equal(int64(1000), power)
		stakingVal, found := stakingKeeper.GetValidatorByConsAddr(s.providerCtx(), sdk.ConsAddress(val.Address))
		if !found {
			s.Require().Fail("validator not found")
		}
		s.Require().False(stakingVal.Jailed)

		// 4th validator should have no slash log, all the others do
		if val != s.providerChain.Vals.Validators[3] {
			s.Require().True(providerKeeper.GetSlashLog(s.providerCtx(),
				providertypes.NewProviderConsAddress([]byte(val.Address))))
		} else {
			s.Require().False(providerKeeper.GetSlashLog(s.providerCtx(),
				providertypes.NewProviderConsAddress([]byte(val.Address))))
		}
	}
}

// TestSlashingSmallValidators tests that multiple slash packets from validators with small
// power can be handled by the provider chain in a non-throttled manner.
func (s *CCVTestSuite) TestSlashingSmallValidators() {
	s.SetupAllCCVChannels()

	// Setup first val with 1000 power and the rest with 10 power.
	delAddr := s.providerChain.SenderAccount.GetAddress()
	delegateByIdx(s, delAddr, sdk.NewInt(999999999), 0)
	delegateByIdx(s, delAddr, sdk.NewInt(9999999), 1)
	delegateByIdx(s, delAddr, sdk.NewInt(9999999), 2)
	delegateByIdx(s, delAddr, sdk.NewInt(9999999), 3)
	s.providerChain.NextBlock()

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
	s.setDefaultValSigningInfo(*s.providerChain.Vals.Validators[2])
	s.setDefaultValSigningInfo(*s.providerChain.Vals.Validators[3])

	// Send slash packets from consumer to provider for small validators.
	var (
		timeoutHeight    = clienttypes.Height{}
		timeoutTimestamp = uint64(s.getFirstBundle().GetCtx().BlockTime().Add(ccvtypes.DefaultCCVTimeoutPeriod).UnixNano())
	)
	tmval1 := s.providerChain.Vals.Validators[1]
	tmval2 := s.providerChain.Vals.Validators[2]
	tmval3 := s.providerChain.Vals.Validators[3]
	slashPacket1 := s.constructSlashPacketFromConsumer(s.getFirstBundle(), *tmval1, stakingtypes.Infraction_INFRACTION_DOWNTIME, 1)
	slashPacket2 := s.constructSlashPacketFromConsumer(s.getFirstBundle(), *tmval2, stakingtypes.Infraction_INFRACTION_DOWNTIME, 2)
	slashPacket3 := s.constructSlashPacketFromConsumer(s.getFirstBundle(), *tmval3, stakingtypes.Infraction_INFRACTION_DOWNTIME, 3)
	sendOnConsumerRecvOnProvider(s, s.getFirstBundle().Path, timeoutHeight, timeoutTimestamp, slashPacket1.GetData())
	sendOnConsumerRecvOnProvider(s, s.getFirstBundle().Path, timeoutHeight, timeoutTimestamp, slashPacket2.GetData())
	sendOnConsumerRecvOnProvider(s, s.getFirstBundle().Path, timeoutHeight, timeoutTimestamp, slashPacket3.GetData())

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
//
// TODO: This should be a unit test, or replaced by TestTotalVotingPowerChanges.
func (s *CCVTestSuite) TestSlashMeterAllowanceChanges() {
	s.SetupAllCCVChannels()

	providerKeeper := s.providerApp.GetProviderKeeper()

	// At first, allowance is based on 4 vals all with 1 power, min allowance is in effect.
	s.Require().Equal(int64(1), providerKeeper.GetSlashMeterAllowance(s.providerCtx()).Int64())

	s.setupValidatorPowers([]int64{1000, 1000, 1000, 1000})

	// Now all 4 validators have 1000 power (4000 total power) so allowance should be:
	// default replenish frac * 4000 = 200
	s.Require().Equal(int64(200), providerKeeper.GetSlashMeterAllowance(s.providerCtx()).Int64())

	// Now we change replenish fraction and assert new expected allowance.
	params := providerKeeper.GetParams(s.providerCtx())
	params.SlashMeterReplenishFraction = "0.3"
	providerKeeper.SetParams(s.providerCtx(), params)
	s.Require().Equal(int64(1200), providerKeeper.GetSlashMeterAllowance(s.providerCtx()).Int64())
}

// Similar to TestSlashSameValidator, but 100% of val power is jailed a single block,
// and in the first packets recv for that block.
// This edge case should not occur in practice, but is useful to validate that
// the slash meter can allow any number of slash packets to be handled in a single block when
// its allowance is set to "1.0".
func (s CCVTestSuite) TestSlashAllValidators() { //nolint:govet // this is a test so we can copy locks

	s.SetupAllCCVChannels()

	// Setup 4 validators with 25% of the total power each.
	s.setupValidatorPowers([]int64{1000, 1000, 1000, 1000})

	providerKeeper := s.providerApp.GetProviderKeeper()

	// Set replenish fraction to 1.0 so that all sent packets should be handled immediately (no throttling)
	params := providerKeeper.GetParams(s.providerCtx())
	params.SlashMeterReplenishFraction = fullSlashMeterString // needs to be const for linter
	providerKeeper.SetParams(s.providerCtx(), params)
	providerKeeper.InitializeSlashMeter(s.providerCtx())

	// The packets to be recv in a single block, ordered as they will be recv.
	var packetsData [][]byte

	// Instantiate a slash packet for each validator,
	// these first 4 packets should jail 100% of the total power.
	ibcSeqNum := uint64(1)
	for _, val := range s.providerChain.Vals.Validators {
		s.setDefaultValSigningInfo(*val)
		packetsData = append(packetsData, s.constructSlashPacketFromConsumer(
			s.getFirstBundle(), *val, stakingtypes.Infraction_INFRACTION_DOWNTIME, ibcSeqNum).GetData())
		ibcSeqNum++
	}

	// add 5 more slash packets for each validator, that will be handled in the same block.
	for _, val := range s.providerChain.Vals.Validators {
		for i := 0; i < 5; i++ {
			packetsData = append(packetsData, s.constructSlashPacketFromConsumer(
				s.getFirstBundle(), *val, stakingtypes.Infraction_INFRACTION_DOWNTIME, ibcSeqNum).GetData())
			ibcSeqNum++
		}
	}

	// Recv and queue all slash packets.
	var (
		timeoutHeight    = clienttypes.Height{}
		timeoutTimestamp = uint64(s.getFirstBundle().GetCtx().BlockTime().Add(ccvtypes.DefaultCCVTimeoutPeriod).UnixNano())
	)
	for i, data := range packetsData {
		ibcSeqNum := uint64(i)
		consumerPacketData, err := provider.UnmarshalConsumerPacketData(data) // Same func used by provider's OnRecvPacket
		s.Require().NoError(err)
		packet := s.newPacketFromConsumer(data, ibcSeqNum, s.getFirstBundle().Path, timeoutHeight, timeoutTimestamp)
		_, err = providerKeeper.OnRecvSlashPacket(s.providerCtx(), packet, *consumerPacketData.GetSlashPacketData())
		s.Require().NoError(err)
	}

	// Check that all validators are jailed.
	for _, val := range s.providerChain.Vals.Validators {
		// Do not check power, since val power is not yet updated by staking endblocker.
		s.confirmValidatorJailed(*val, false)
	}

	// Nextblock would fail the test now, since ibctesting fails when
	// "applying the validator changes would result in empty set".
}

func (s *CCVTestSuite) confirmValidatorJailed(tmVal tmtypes.Validator, checkPower bool) {
	sdkVal, found := s.providerApp.GetTestStakingKeeper().GetValidator(
		s.providerCtx(), sdk.ValAddress(tmVal.Address))
	s.Require().True(found)
	s.Require().True(sdkVal.IsJailed())

	if checkPower {
		valPower := s.providerApp.GetTestStakingKeeper().GetLastValidatorPower(
			s.providerCtx(), sdkVal.GetOperator())
		s.Require().Equal(int64(0), valPower)
	}
}

func (s *CCVTestSuite) confirmValidatorNotJailed(tmVal tmtypes.Validator, expectedPower int64) {
	sdkVal, found := s.providerApp.GetTestStakingKeeper().GetValidator(
		s.providerCtx(), sdk.ValAddress(tmVal.Address))
	s.Require().True(found)
	valPower := s.providerApp.GetTestStakingKeeper().GetLastValidatorPower(
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

func (s *CCVTestSuite) getCtxAfterReplenishCandidate(ctx sdk.Context) sdk.Context {
	providerKeeper := s.providerApp.GetProviderKeeper()
	candidate := providerKeeper.GetSlashMeterReplenishTimeCandidate(ctx)
	return ctx.WithBlockTime(candidate.Add(time.Minute))
}
