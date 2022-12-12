package keeper_test

import (
	"math/rand"
	"testing"
	"time"

	"github.com/cosmos/interchain-security/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"
	"github.com/golang/mock/gomock"

	sdktypes "github.com/cosmos/cosmos-sdk/types"
	cryptoutil "github.com/cosmos/interchain-security/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	"github.com/stretchr/testify/require"
	tmtypes "github.com/tendermint/tendermint/types"
	"golang.org/x/exp/slices"
)

// TestHandlePacketDataForChain tests the HandlePacketDataForChain function. Note: Only one consumer is tested here,
// but multiple consumers are tested in TestPendingPacketData.
func TestHandlePacketDataForChain(t *testing.T) {

	testCases := []struct {
		name    string
		chainID string
		// Pending packet data that will be queued in the order specified by the slice
		dataToQueue []interface{}
		// Indexes of packet data from dataToQueue that are expected to be handled and deleted from store
		expectedHandledIndexes []int
	}{
		{
			"no packets",
			"my-cool-chain",
			[]interface{}{},
			[]int{},
		},
		{
			"one slash packet should be handled",
			"chain-37",
			[]interface{}{
				testkeeper.GetNewSlashPacketData(),
			},
			[]int{0},
		},
		{
			"one slash packet followed by one vsc matured packet should all be handled",
			"chain-222",
			[]interface{}{
				testkeeper.GetNewSlashPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
			},
			[]int{0, 1},
		},
		{
			"one slash packet followed by multiple vsc matured packets should all be handled",
			"chain-2223",
			[]interface{}{
				testkeeper.GetNewSlashPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
			},
			[]int{0, 1, 2, 3, 4, 5},
		},
		{
			"multiple slash packets followed by multiple vsc matured packets should only handle first slash packet",
			"chain-9",
			[]interface{}{
				testkeeper.GetNewSlashPacketData(),
				testkeeper.GetNewSlashPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
			},
			[]int{0},
		},
		{
			"vsc matured packets sandwiched between slash packets should handle everything but the last slash packet",
			"chain-000",
			[]interface{}{
				testkeeper.GetNewSlashPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewSlashPacketData(), // 10th index not included in expectedHandledIndexes
			},
			[]int{0, 1, 2, 3, 4, 5, 6, 7, 8, 9},
		},
		{
			"alternating slash and vsc matured packets should handle only the first slash, and trailing vsc matured packets",
			"chain-00000",
			[]interface{}{
				testkeeper.GetNewSlashPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewSlashPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewSlashPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewSlashPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
				testkeeper.GetNewSlashPacketData(),
				testkeeper.GetNewVSCMaturedPacketData(),
			},
			[]int{0, 1, 2},
		},
	}

	for _, tc := range testCases {
		providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
		defer ctrl.Finish()
		providerKeeper.SetParams(ctx, providertypes.DefaultParams())

		// Queue pending packet data, where chainID is arbitrary, and ibc seq number is index of the data instance
		for i, data := range tc.dataToQueue {
			providerKeeper.QueuePendingPacketData(ctx, tc.chainID, uint64(i), data)
		}

		// Define our handler callbacks to simply store the data instances that are handled
		handledData := []interface{}{}
		slashHandleCounter := func(ctx sdktypes.Context, chainID string, data ccvtypes.SlashPacketData) {
			handledData = append(handledData, data)
		}
		vscMaturedHandleCounter := func(ctx sdktypes.Context, chainID string, data ccvtypes.VSCMaturedPacketData) {
			handledData = append(handledData, data)
		}

		providerKeeper.HandlePacketDataForChain(ctx, tc.chainID, slashHandleCounter, vscMaturedHandleCounter)

		// Assert number of handled data instances matches expected number
		require.Equal(t, len(tc.expectedHandledIndexes), len(handledData))

		// Assert handled data instances match expected value
		for i, expectedIndex := range tc.expectedHandledIndexes {
			require.Equal(t, tc.dataToQueue[expectedIndex], handledData[i])
		}

		// Sanity check, Assert that only the first handled packet is a slash packet, and the rest are vsc matured packets
		for idx, instance := range handledData {
			switch instance.(type) {
			case ccvtypes.SlashPacketData:
				require.Equal(t, 0, idx)
			case ccvtypes.VSCMaturedPacketData:
			default:
				require.Fail(t, "unexpected data instance type")
			}
		}

		// Assert that the unhandled queued data instances are as expected (i.e no unexpected deletions)
		expectedDataThatsLeft := []interface{}{}
		for idx, data := range tc.dataToQueue {
			if !slices.Contains(tc.expectedHandledIndexes, idx) {
				expectedDataThatsLeft = append(expectedDataThatsLeft, data)
			}
		}

		dataThatsLeft := []interface{}{}
		providerKeeper.IteratePendingPacketData(ctx, tc.chainID, func(ibcSeqNum uint64, data interface{}) bool {
			dataThatsLeft = append(dataThatsLeft, data)
			return false
		})

		require.Equal(t, expectedDataThatsLeft, dataThatsLeft)

		// Assert that each instance of handled data is deleted from the persisted queue (i.e deletions where expected)
		for _, dataInstance := range handledData {
			require.NotContains(t, dataThatsLeft, dataInstance)
		}
	}
}

// TestSlashMeterReplenishment tests the CheckForSlashMeterReplenishment, ReplenishSlashMeter,
// and InitializeSlashMeter methods.
func TestSlashMeterReplenishment(t *testing.T) {
	testCases := []struct {
		replenishPeriod   time.Duration
		replenishFraction string
		totalPower        sdktypes.Int
		// Replenish fraction * total power, also serves as max slash meter value
		expectedAllowance sdktypes.Int
	}{
		{
			replenishPeriod:   time.Minute,
			replenishFraction: "0.01",
			totalPower:        sdktypes.NewInt(1000),
			expectedAllowance: sdktypes.NewInt(10),
		},
		{
			replenishPeriod:   time.Hour,
			replenishFraction: "0.1",
			totalPower:        sdktypes.NewInt(100000),
			expectedAllowance: sdktypes.NewInt(10000),
		},
		{
			replenishPeriod:   30 * time.Minute,
			replenishFraction: "0.5",
			totalPower:        sdktypes.NewInt(1000000000000000),
			expectedAllowance: sdktypes.NewInt(500000000000000),
		},
	}
	for _, tc := range testCases {

		providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(
			t, testkeeper.NewInMemKeeperParams(t))
		defer ctrl.Finish()

		now := time.Now()
		ctx = ctx.WithBlockTime(now)

		// Set desired params
		params := providertypes.DefaultParams()
		params.SlashMeterReplenishPeriod = tc.replenishPeriod
		params.SlashMeterReplenishFraction = tc.replenishFraction
		providerKeeper.SetParams(ctx, params)

		// Mock total power from staking keeper using test case value
		// Any ctx is accepted, and the method will be called multiple times during the tests
		gomock.InOrder(
			mocks.MockStakingKeeper.EXPECT().GetLastTotalPower(
				gomock.Any()).Return(tc.totalPower).AnyTimes(),
		)

		// Now we can initialize the slash meter (this would happen in InitGenesis)
		providerKeeper.InitializeSlashMeter(ctx)

		// Confirm meter value is initialized to expected allowance
		require.Equal(t, tc.expectedAllowance, providerKeeper.GetSlashMeter(ctx))

		// Confirm last full time is current block time.
		require.Equal(t, now.UTC(), providerKeeper.GetLastSlashMeterFullTime(ctx))

		// Decrement slash meter
		providerKeeper.SetSlashMeter(ctx, providerKeeper.GetSlashMeter(ctx).Sub(sdktypes.NewInt(3)))
		require.Equal(t, tc.expectedAllowance.Sub(sdktypes.NewInt(3)), providerKeeper.GetSlashMeter(ctx))

		// Check for replenishment, confirm meter is not replenished (since no time has passed since init)
		meterBefore := providerKeeper.GetSlashMeter(ctx)
		providerKeeper.CheckForSlashMeterReplenishment(ctx)
		require.Equal(t, meterBefore, providerKeeper.GetSlashMeter(ctx))

		// Confirm last full time is not updated
		require.Equal(t, now.UTC(), providerKeeper.GetLastSlashMeterFullTime(ctx))

		// Note: odd time formats are used as an extra sanity check that UTC format is persisted

		// Increment block time by half replenish period
		ctx = ctx.WithBlockTime(now.Add(tc.replenishPeriod / 2).Local())

		// Confirm meter is not still not replenished
		meterBefore = providerKeeper.GetSlashMeter(ctx)
		providerKeeper.CheckForSlashMeterReplenishment(ctx)
		require.Equal(t, meterBefore, providerKeeper.GetSlashMeter(ctx))

		// Confirm last full time is not updated
		require.Equal(t, now.UTC(), providerKeeper.GetLastSlashMeterFullTime(ctx))

		// Increment block time by more than replenish period
		ctx = ctx.WithBlockTime(now.Add(tc.replenishPeriod * 2).In(time.FixedZone("UTC-8", -8*60*60)))

		// Confirm meter is now replenished to max value
		providerKeeper.CheckForSlashMeterReplenishment(ctx)
		require.Equal(t, tc.expectedAllowance, providerKeeper.GetSlashMeter(ctx))

		// Last full time should now be updated
		require.Equal(t, ctx.BlockTime().UTC(), providerKeeper.GetLastSlashMeterFullTime(ctx))

		// increment block time by more than replenish period again
		ctx = ctx.WithBlockTime(ctx.BlockTime().Add(tc.replenishPeriod * 2))

		// Confirm that meter is capped at max value
		providerKeeper.CheckForSlashMeterReplenishment(ctx)
		require.Equal(t, tc.expectedAllowance, providerKeeper.GetSlashMeter(ctx))

		// Confirm last full time is updated, even though slash meter was not replenished
		require.Equal(t, ctx.BlockTime().UTC(), providerKeeper.GetLastSlashMeterFullTime(ctx))
	}
}

// TestSlashMeterAllowanceChanges tests the behavior of a full slash meter
// when total voting power becomes higher and lower.
func TestTotalVotingPowerChanges(t *testing.T) {

	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	now := time.Now()
	ctx = ctx.WithBlockTime(now)

	params := providertypes.DefaultParams()
	params.SlashMeterReplenishFraction = "0.1"
	params.SlashMeterReplenishPeriod = time.Hour
	providerKeeper.SetParams(ctx, params)

	// Mock total power to be 1000
	gomock.InOrder(
		mocks.MockStakingKeeper.EXPECT().GetLastTotalPower(
			// Expect two calls, once for initialization, once for allowance check
			ctx).Return(sdktypes.NewInt(1000)).Times(2),
	)

	// Initialize the slash meter (this would happen in InitGenesis)
	providerKeeper.InitializeSlashMeter(ctx)

	// Confirm slash meter is full, and allowance is expected value via params
	require.Equal(t, sdktypes.NewInt(100), providerKeeper.GetSlashMeterAllowance(ctx))
	require.Equal(t, sdktypes.NewInt(100), providerKeeper.GetSlashMeter(ctx))

	// Mutate context so mocked total power is less than before
	ctx = ctx.WithBlockTime(ctx.BlockTime().Add(time.Microsecond)) // Don't add enough time for replenishment
	gomock.InOrder(
		mocks.MockStakingKeeper.EXPECT().GetLastTotalPower(
			// Expect two calls, once for replenish check, once for allowance check
			ctx).Return(sdktypes.NewInt(500)).Times(2),
	)

	// Replenishment should not happen here, but slash meter should be decremented to new allowance
	providerKeeper.CheckForSlashMeterReplenishment(ctx)
	require.Equal(t, sdktypes.NewInt(50), providerKeeper.GetSlashMeterAllowance(ctx))
	require.Equal(t, sdktypes.NewInt(50), providerKeeper.GetSlashMeter(ctx))

	// Mutate context so mocked total power is again less than before,
	// with ctx time set to a time that will replenish meter
	ctx = ctx.WithBlockTime(ctx.BlockTime().Add(5 * time.Hour))
	gomock.InOrder(
		mocks.MockStakingKeeper.EXPECT().GetLastTotalPower(
			// Expect three calls, once for replenish check,
			// once for replenishment, once for allowance check
			ctx).Return(sdktypes.NewInt(100)).Times(3),
	)

	// Replenishment should happen here, slash meter should be decremented to new allowance regardless
	providerKeeper.CheckForSlashMeterReplenishment(ctx)
	require.Equal(t, sdktypes.NewInt(10), providerKeeper.GetSlashMeterAllowance(ctx))
	require.Equal(t, sdktypes.NewInt(10), providerKeeper.GetSlashMeter(ctx))

	// Mutate context so mocked total power is now more than before
	ctx = ctx.WithBlockTime(ctx.BlockTime().Add(time.Microsecond)) // Don't add enough time for replenishment
	gomock.InOrder(
		mocks.MockStakingKeeper.EXPECT().GetLastTotalPower(
			// Expect two calls, once for replenish check, once for allowance check
			ctx).Return(sdktypes.NewInt(5000)).Times(2),
	)

	//
	// Important: Without a replenishment, the meter should remain at its previous value
	//

	// Replenishment should not happen here, slash meter should remain at previous value
	providerKeeper.CheckForSlashMeterReplenishment(ctx)
	require.Equal(t, sdktypes.NewInt(500), providerKeeper.GetSlashMeterAllowance(ctx))
	require.Equal(t, sdktypes.NewInt(10), providerKeeper.GetSlashMeter(ctx))

	// Mutate context so mocked total power is again more than before,
	// with ctx time set to a time that will replenish meter
	ctx = ctx.WithBlockTime(ctx.BlockTime().Add(5 * time.Hour))
	gomock.InOrder(
		mocks.MockStakingKeeper.EXPECT().GetLastTotalPower(
			// Expect three calls, once for replenish check,
			// once for replenishment, once for allowance check
			ctx).Return(sdktypes.NewInt(10000)).Times(3),
	)

	// Replenishment should happen here, slash meter should be set to new allowance
	providerKeeper.CheckForSlashMeterReplenishment(ctx)
	require.Equal(t, sdktypes.NewInt(1000), providerKeeper.GetSlashMeterAllowance(ctx))
	require.Equal(t, sdktypes.NewInt(1000), providerKeeper.GetSlashMeter(ctx))
}

// TestNegativeSlashMeter tests behavior of the slash meter when it goes negative,
// and also the fact that the replenishment allowance becomes lower as total
// voting power becomes lower from slashing.
func TestNegativeSlashMeter(t *testing.T) {

	testCases := []struct {
		slashedPower           sdktypes.Int
		totalPower             sdktypes.Int
		replenishFraction      string
		numReplenishesTillFull int
		finalMeterValue        sdktypes.Int
	}{
		{
			// Meter is initialized to a value of: 0.01*1000 = 10.
			// Slashing 100 of voting power makes total voting power = 900, and meter = -90.
			// Expected replenish allowance is then 9, meaning it'd take 10 replenishes
			// for meter to reach 0 in value, and 11 replenishes for meter to reach a value of 9.
			slashedPower:           sdktypes.NewInt(100),
			totalPower:             sdktypes.NewInt(1000),
			replenishFraction:      "0.01",
			numReplenishesTillFull: 11,
			finalMeterValue:        sdktypes.NewInt(9),
		},
		{
			// Meter is initialized to a value of: 0.1*100 = 10.
			// Slashing 30 of voting power makes total voting power = 70, and meter = -20.
			// Expected replenish allowance is then 7, meaning it'd take 3 replenishes
			// for meter to reach 1 in value, and 4 replenishes for meter to reach a value of 7.
			slashedPower:           sdktypes.NewInt(30),
			totalPower:             sdktypes.NewInt(100),
			replenishFraction:      "0.1",
			numReplenishesTillFull: 4,
			finalMeterValue:        sdktypes.NewInt(7),
		},
		{
			// Meter is initialized to a value of 1, since replenish fraction is too low, and min allowance is 1.
			// Slashing 5 of voting power makes total voting power = 995, and meter = -4.
			// Expected replenish allowance is then 1 (still minimum amount), meaning it'd take 4 replenishes
			// for meter to reach 0 in value, and 5 replenishes for meter to reach a value of 1.
			slashedPower:           sdktypes.NewInt(5),
			totalPower:             sdktypes.NewInt(1000),
			replenishFraction:      "0.0000001",
			numReplenishesTillFull: 5,
			finalMeterValue:        sdktypes.NewInt(1),
		},
	}

	for _, tc := range testCases {
		providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(
			t, testkeeper.NewInMemKeeperParams(t))
		defer ctrl.Finish()

		params := providertypes.DefaultParams()
		params.SlashMeterReplenishFraction = tc.replenishFraction
		providerKeeper.SetParams(ctx, params)

		// Return mocked values: total power once,
		// then total power minus slashed power any amount of times
		gomock.InOrder(
			mocks.MockStakingKeeper.EXPECT().GetLastTotalPower(
				gomock.Any()).Return(tc.totalPower).Times(1),
			mocks.MockStakingKeeper.EXPECT().GetLastTotalPower(
				gomock.Any()).Return(tc.totalPower.Sub(tc.slashedPower)).AnyTimes(),
		)

		// Initialize the slash meter (using first mocked value)
		providerKeeper.InitializeSlashMeter(ctx)

		// remaining calls to GetLastTotalPower should return the second mocked value.

		// Confirm that meter is initialized to expected initial allowance
		decFrac, err := sdktypes.NewDecFromStr(tc.replenishFraction)
		require.NoError(t, err)
		expectedInitAllowance := sdktypes.NewInt(decFrac.MulInt(tc.totalPower).RoundInt64())
		if expectedInitAllowance.IsZero() { // Allowances have a minimum of 1.
			expectedInitAllowance = sdktypes.NewInt(1)
		}
		require.Equal(t, expectedInitAllowance, providerKeeper.GetSlashMeter(ctx))

		// Decrement meter by slashed amount, simulating a validator getting slashed
		before := providerKeeper.GetSlashMeter(ctx)
		providerKeeper.SetSlashMeter(ctx, before.Sub(tc.slashedPower))
		require.True(t, providerKeeper.GetSlashMeter(ctx).LT(before))

		// New expected allowance is replenish fraction * (total power - slashed power)
		expectedNewAllowance := sdktypes.NewInt(decFrac.MulInt(tc.totalPower.Sub(tc.slashedPower)).RoundInt64())
		if expectedNewAllowance.IsZero() {
			expectedNewAllowance = sdktypes.NewInt(1)
		}
		require.Equal(t, expectedNewAllowance, providerKeeper.GetSlashMeterAllowance(ctx))

		// Execute all but last expected replenishment
		for i := 0; i < tc.numReplenishesTillFull-1; i++ {
			providerKeeper.ReplenishSlashMeter(ctx)
			currValue := providerKeeper.GetSlashMeter(ctx)
			if currValue.Equal(expectedNewAllowance) {
				require.Fail(t, "slash meter should not be replenished to max value yet")
			}
		}

		// Execute last expected replenishment
		providerKeeper.ReplenishSlashMeter(ctx)

		// Confirm meter is equal to new allowance (which is also new max value)
		meter := providerKeeper.GetSlashMeter(ctx)
		require.EqualValues(t, expectedNewAllowance, meter)

		// Confirm meter is capped at max value even with another replenishment,
		// and this matches the expected final value
		providerKeeper.ReplenishSlashMeter(ctx)
		require.Equal(t, meter, providerKeeper.GetSlashMeter(ctx),
			"slash meter value should not have changed")
		require.Equal(t, tc.finalMeterValue, providerKeeper.GetSlashMeter(ctx))
	}
}

// TestGetSlashMeterAllowance is a granular unit test validating the behavior
// (specifically around rounding) of the GetSlashMeterAllowance method.
func TestGetSlashMeterAllowance(t *testing.T) {
	testCases := []struct {
		replenishFraction string
		totalPower        sdktypes.Int
		// Replenish fraction * total power
		expectedAllowance sdktypes.Int
	}{
		{
			replenishFraction: "0.00",
			totalPower:        sdktypes.NewInt(100),
			expectedAllowance: sdktypes.NewInt(1), // 0.0 * 100 = 0, 1 is returned
		},
		{
			replenishFraction: "0.00000000001",
			totalPower:        sdktypes.NewInt(100),
			expectedAllowance: sdktypes.NewInt(1), // 0.00000000001 * 100 = 0 (bankers rounding), 1 is returned
		},
		{
			replenishFraction: "0.01",
			totalPower:        sdktypes.NewInt(100),
			expectedAllowance: sdktypes.NewInt(1), // 0.00000000001 * 100 = 0 (bankers rounding), 1 is returned
		},
		{
			replenishFraction: "0.015",
			totalPower:        sdktypes.NewInt(100),
			expectedAllowance: sdktypes.NewInt(2), // 0.015 * 10 = 2 (bankers rounding)
		},
		{
			replenishFraction: "0.27",
			totalPower:        sdktypes.NewInt(100),
			expectedAllowance: sdktypes.NewInt(27),
		},
		{
			replenishFraction: "0.34",
			totalPower:        sdktypes.NewInt(10000000),
			expectedAllowance: sdktypes.NewInt(3400000),
		},
	}
	for _, tc := range testCases {

		providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(
			t, testkeeper.NewInMemKeeperParams(t))
		defer ctrl.Finish()

		gomock.InOrder(
			mocks.MockStakingKeeper.EXPECT().GetLastTotalPower(
				gomock.Any()).Return(tc.totalPower).Times(1),
		)

		// Set desired params
		params := providertypes.DefaultParams()
		params.SlashMeterReplenishFraction = tc.replenishFraction
		providerKeeper.SetParams(ctx, params)

		// Confirm allowance is calculated correctly
		require.Equal(t, tc.expectedAllowance,
			providerKeeper.GetSlashMeterAllowance(ctx))
	}
}

// TestGlobalSlashEntries tests the queue and iteration functions for global slash entries,
// with assertion of FIFO ordering
func TestPendingSlashPacketEntries(t *testing.T) {

	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// Consistent time for "now"
	now := time.Now().UTC()

	globalEntries := providerKeeper.GetAllGlobalSlashEntries(ctx)
	require.Equal(t, 0, len(globalEntries))

	// Queue 3 entries for chainIDs 0, 1, 2, note their respective ibc seq nums are
	// ordered differently than the chainIDs would be iterated.
	providerKeeper.QueueGlobalSlashEntry(ctx, providertypes.NewGlobalSlashEntry(
		now.Local(), "chain-0", 15, cryptoutil.NewCryptoIdentityFromIntSeed(10).SDKConsAddress()))
	providerKeeper.QueueGlobalSlashEntry(ctx, providertypes.NewGlobalSlashEntry(
		now.Local(), "chain-1", 10, cryptoutil.NewCryptoIdentityFromIntSeed(11).SDKConsAddress()))
	providerKeeper.QueueGlobalSlashEntry(ctx, providertypes.NewGlobalSlashEntry(
		now.Local(), "chain-2", 5, cryptoutil.NewCryptoIdentityFromIntSeed(12).SDKConsAddress()))

	globalEntries = providerKeeper.GetAllGlobalSlashEntries(ctx)
	require.Equal(t, 3, len(globalEntries))

	// Queue 3 entries for chainIDs 0, 1, 2 an hour later, with incremented ibc seq nums
	providerKeeper.QueueGlobalSlashEntry(ctx, providertypes.NewGlobalSlashEntry(
		now.Add(time.Hour).Local(), "chain-0", 16, // should appear last for this recv time
		cryptoutil.NewCryptoIdentityFromIntSeed(20).SDKConsAddress()))
	providerKeeper.QueueGlobalSlashEntry(ctx, providertypes.NewGlobalSlashEntry(
		now.Add(time.Hour).Local(), "chain-1", 11, // should appear middle for this recv time
		cryptoutil.NewCryptoIdentityFromIntSeed(21).SDKConsAddress()))
	providerKeeper.QueueGlobalSlashEntry(ctx, providertypes.NewGlobalSlashEntry(
		now.Add(time.Hour).Local(), "chain-2", 6, // should appear first for this recv time
		cryptoutil.NewCryptoIdentityFromIntSeed(22).SDKConsAddress()))

	// Retrieve entries from store
	globalEntries = providerKeeper.GetAllGlobalSlashEntries(ctx)
	require.Equal(t, 6, len(globalEntries))

	// Assert that entries are obtained in FIFO order according to block time, then ibc seq num
	require.Equal(t, "chain-2", globalEntries[0].ConsumerChainID)
	require.Equal(t, "chain-1", globalEntries[1].ConsumerChainID)
	require.Equal(t, "chain-0", globalEntries[2].ConsumerChainID)
	require.Equal(t, "chain-2", globalEntries[3].ConsumerChainID)
	require.Equal(t, "chain-1", globalEntries[4].ConsumerChainID)
	require.Equal(t, "chain-0", globalEntries[5].ConsumerChainID)

	// Queue 3 entries for chainIDs 5, 6, 7 another hour later
	providerKeeper.QueueGlobalSlashEntry(ctx,
		providertypes.NewGlobalSlashEntry(now.Add(2*time.Hour).Local(), "chain-5", 50, // should appear middle for this recv time
			cryptoutil.NewCryptoIdentityFromIntSeed(96).SDKConsAddress()))
	providerKeeper.QueueGlobalSlashEntry(ctx,
		providertypes.NewGlobalSlashEntry(now.Add(2*time.Hour).Local(), "chain-6", 60, // should appear last for this recv time
			cryptoutil.NewCryptoIdentityFromIntSeed(97).SDKConsAddress()))
	providerKeeper.QueueGlobalSlashEntry(ctx,
		providertypes.NewGlobalSlashEntry(now.Add(2*time.Hour).Local(), "chain-7", 40, // should appear first for this recv time
			cryptoutil.NewCryptoIdentityFromIntSeed(98).SDKConsAddress()))

	// Retrieve entries from store
	globalEntries = providerKeeper.GetAllGlobalSlashEntries(ctx)
	require.Equal(t, 9, len(globalEntries))

	// Assert that entries are obtained in FIFO order according to block time, then ibc seq num
	require.Equal(t, "chain-2", globalEntries[0].ConsumerChainID)
	require.Equal(t, "chain-1", globalEntries[1].ConsumerChainID)
	require.Equal(t, "chain-0", globalEntries[2].ConsumerChainID)
	require.Equal(t, "chain-2", globalEntries[3].ConsumerChainID)
	require.Equal(t, "chain-1", globalEntries[4].ConsumerChainID)
	require.Equal(t, "chain-0", globalEntries[5].ConsumerChainID)
	require.Equal(t, "chain-7", globalEntries[6].ConsumerChainID)
	require.Equal(t, "chain-5", globalEntries[7].ConsumerChainID)
	require.Equal(t, "chain-6", globalEntries[8].ConsumerChainID)

	// Assert each field is as expected for all 9 entries
	require.Equal(t, uint64(5), globalEntries[0].IbcSeqNum)
	require.Equal(t, uint64(10), globalEntries[1].IbcSeqNum)
	require.Equal(t, uint64(15), globalEntries[2].IbcSeqNum)
	require.Equal(t, uint64(6), globalEntries[3].IbcSeqNum)
	require.Equal(t, uint64(11), globalEntries[4].IbcSeqNum)
	require.Equal(t, uint64(16), globalEntries[5].IbcSeqNum)
	require.Equal(t, uint64(40), globalEntries[6].IbcSeqNum)
	require.Equal(t, uint64(50), globalEntries[7].IbcSeqNum)
	require.Equal(t, uint64(60), globalEntries[8].IbcSeqNum)

	require.Equal(t, now, globalEntries[0].RecvTime)
	require.Equal(t, now, globalEntries[1].RecvTime)
	require.Equal(t, now, globalEntries[2].RecvTime)
	require.Equal(t, now.Add(time.Hour).UTC(), globalEntries[3].RecvTime)
	require.Equal(t, now.Add(time.Hour).UTC(), globalEntries[4].RecvTime)
	require.Equal(t, now.Add(time.Hour).UTC(), globalEntries[5].RecvTime)
	require.Equal(t, now.Add(2*time.Hour).UTC(), globalEntries[6].RecvTime)
	require.Equal(t, now.Add(2*time.Hour).UTC(), globalEntries[7].RecvTime)
	require.Equal(t, now.Add(2*time.Hour).UTC(), globalEntries[8].RecvTime)

	// Test the callback break functionality of the iterator
	globalEntries = []providertypes.GlobalSlashEntry{}
	providerKeeper.IterateGlobalSlashEntries(ctx, func(entry providertypes.GlobalSlashEntry) bool {
		globalEntries = append(globalEntries, entry)
		// Break after any of the third set of entries is seen
		stop := entry.ConsumerChainID == "chain-7" || entry.ConsumerChainID == "chain-6" || entry.ConsumerChainID == "chain-5"
		return stop
	})
	// Expect first two sets of entries to be seen, and one packet from the third set
	require.Equal(t, 7, len(globalEntries))
}

// Tests DeleteGlobalSlashEntriesForConsumer.
func TestDeleteGlobalSlashEntriesForConsumer(t *testing.T) {

	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(
		t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// Queue 2 global entries for a consumer chain ID
	providerKeeper.QueueGlobalSlashEntry(ctx,
		providertypes.NewGlobalSlashEntry(time.Now().Add(time.Hour), "chain-78", 1,
			cryptoutil.NewCryptoIdentityFromIntSeed(78).SDKConsAddress()))
	providerKeeper.QueueGlobalSlashEntry(ctx,
		providertypes.NewGlobalSlashEntry(time.Now().Add(time.Hour), "chain-78", 2,
			cryptoutil.NewCryptoIdentityFromIntSeed(79).SDKConsAddress()))

	// Queue 1 global entry for two other consumer chain IDs
	providerKeeper.QueueGlobalSlashEntry(ctx,
		providertypes.NewGlobalSlashEntry(time.Now().Add(2*time.Hour), "chain-79", 1,
			cryptoutil.NewCryptoIdentityFromIntSeed(80).SDKConsAddress()))

	providerKeeper.QueueGlobalSlashEntry(ctx,
		providertypes.NewGlobalSlashEntry(time.Now().Add(3*time.Hour), "chain-80", 1,
			cryptoutil.NewCryptoIdentityFromIntSeed(81).SDKConsAddress()))

	// Delete entries for chain-78, confirm those are deleted, and the other two remain
	providerKeeper.DeleteGlobalSlashEntriesForConsumer(ctx, "chain-78")
	allEntries := providerKeeper.GetAllGlobalSlashEntries(ctx)
	require.Equal(t, 2, len(allEntries))
	require.Equal(t, "chain-79", allEntries[0].ConsumerChainID)
	require.Equal(t, "chain-80", allEntries[1].ConsumerChainID)
}

// TestGlobalSlashEntryDeletion tests the deletion function for
// global slash entries with assertion of FIFO ordering.
func TestGlobalSlashEntryDeletion(t *testing.T) {

	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	now := time.Now()

	entries := providerKeeper.GetAllGlobalSlashEntries(ctx)
	require.Equal(t, 0, len(entries))

	// Instantiate entries in the expected order we wish to get them back as (ordered by recv time)
	entries = []providertypes.GlobalSlashEntry{}
	entries = append(entries, providertypes.NewGlobalSlashEntry(now, "chain-0", 1, cryptoutil.NewCryptoIdentityFromIntSeed(0).SDKConsAddress()))
	entries = append(entries, providertypes.NewGlobalSlashEntry(now.Add(time.Hour).UTC(), "chain-1", 178, cryptoutil.NewCryptoIdentityFromIntSeed(1).SDKConsAddress()))
	entries = append(entries, providertypes.NewGlobalSlashEntry(now.Add(2*time.Hour).Local(), "chain-2", 89, cryptoutil.NewCryptoIdentityFromIntSeed(2).SDKConsAddress()))
	entries = append(entries, providertypes.NewGlobalSlashEntry(now.Add(3*time.Hour).In(time.FixedZone("UTC-8", -8*60*60)), "chain-3", 23423, cryptoutil.NewCryptoIdentityFromIntSeed(3).SDKConsAddress()))
	entries = append(entries, providertypes.NewGlobalSlashEntry(now.Add(4*time.Hour).Local(), "chain-4", 323, cryptoutil.NewCryptoIdentityFromIntSeed(4).SDKConsAddress()))
	entries = append(entries, providertypes.NewGlobalSlashEntry(now.Add(5*time.Hour).UTC(), "chain-5", 18, cryptoutil.NewCryptoIdentityFromIntSeed(5).SDKConsAddress()))
	entries = append(entries, providertypes.NewGlobalSlashEntry(now.Add(6*time.Hour).Local(), "chain-6", 2, cryptoutil.NewCryptoIdentityFromIntSeed(6).SDKConsAddress()))

	// Instantiate shuffled copy of above slice
	shuffledEntries := append([]providertypes.GlobalSlashEntry{}, entries...)
	rand.Seed(now.UnixNano())
	rand.Shuffle(len(shuffledEntries), func(i, j int) {
		shuffledEntries[i], shuffledEntries[j] = shuffledEntries[j], shuffledEntries[i]
	})

	// Queue 7 slash packets with various block times in random order
	for _, entry := range shuffledEntries {
		providerKeeper.QueueGlobalSlashEntry(ctx, entry)
	}

	gotEntries := providerKeeper.GetAllGlobalSlashEntries(ctx)
	require.Equal(t, 7, len(gotEntries))

	// Assert obtained order is decided upon via packet recvTime, not insertion order
	for i, gotEntry := range gotEntries {
		expectedEntry := entries[i]
		require.Equal(t, expectedEntry, gotEntry)
	}

	// Confirm no mutations have occurred from test helper
	gotEntries = providerKeeper.GetAllGlobalSlashEntries(ctx)
	require.Equal(t, 7, len(gotEntries))

	// Delete packets 1, 3, 5 (0-indexed)
	providerKeeper.DeleteGlobalSlashEntries(ctx, gotEntries[1], gotEntries[3], gotEntries[5])

	// Assert deletion and ordering
	gotEntries = providerKeeper.GetAllGlobalSlashEntries(ctx)
	require.Equal(t, 4, len(gotEntries))
	require.Equal(t, "chain-0", gotEntries[0].ConsumerChainID)
	// entry 1 was deleted
	require.Equal(t, "chain-2", gotEntries[1].ConsumerChainID)
	// entry 3 was deleted
	require.Equal(t, "chain-4", gotEntries[2].ConsumerChainID)
	// entry 5 was deleted
	require.Equal(t, "chain-6", gotEntries[3].ConsumerChainID)
}

// TestPendingPacketData tests the pending packet data queuing, iteration and deletion functionality.
func TestPendingPacketData(t *testing.T) {

	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()
	providerKeeper.SetParams(ctx, providertypes.DefaultParams())

	packetDataForMultipleConsumers := []struct {
		chainID   string
		instances []pendingPacketDataInstance

		// Expected order of data instances after retrieval from store, before deletion (specified by instance index)
		expectedOrder []int
		// Data instances to delete (specified by instance index)
		toDelete []int
		// Expected order of data instances after deletion (specified by instance index)
		expectedOrderAfterDeletion []int
	}{
		// Note, duplicate ibc sequence numbers are not tested, as we assume ibc behaves correctly
		{
			chainID: "chain-0",
			instances: []pendingPacketDataInstance{
				{IbcSeqNum: 0, Data: testkeeper.GetNewSlashPacketData()},
				{IbcSeqNum: 1, Data: testkeeper.GetNewVSCMaturedPacketData()},
				{IbcSeqNum: 2, Data: testkeeper.GetNewSlashPacketData()},
				{IbcSeqNum: 3, Data: testkeeper.GetNewVSCMaturedPacketData()},
				{IbcSeqNum: 4, Data: testkeeper.GetNewSlashPacketData()},
			},
			expectedOrder:              []int{0, 1, 2, 3, 4},
			toDelete:                   []int{0, 2, 4},
			expectedOrderAfterDeletion: []int{1, 3},
		},
		{
			chainID: "chain-7",
			instances: []pendingPacketDataInstance{
				{IbcSeqNum: 96, Data: testkeeper.GetNewSlashPacketData()},
				{IbcSeqNum: 78, Data: testkeeper.GetNewVSCMaturedPacketData()},
				{IbcSeqNum: 12, Data: testkeeper.GetNewSlashPacketData()},
				{IbcSeqNum: 0, Data: testkeeper.GetNewVSCMaturedPacketData()},
				{IbcSeqNum: 1, Data: testkeeper.GetNewSlashPacketData()},
				{IbcSeqNum: 78972, Data: testkeeper.GetNewVSCMaturedPacketData()},
				{IbcSeqNum: 9999999999999999999, Data: testkeeper.GetNewSlashPacketData()},
			},
			expectedOrder:              []int{3, 4, 2, 1, 0, 5, 6},
			toDelete:                   []int{0, 1, 2, 3, 4, 5},
			expectedOrderAfterDeletion: []int{6},
		},
		{
			chainID: "chain-thats-not-0-or-7",
			instances: []pendingPacketDataInstance{
				{IbcSeqNum: 9, Data: testkeeper.GetNewSlashPacketData()},
				{IbcSeqNum: 8, Data: testkeeper.GetNewSlashPacketData()},
				{IbcSeqNum: 7, Data: testkeeper.GetNewSlashPacketData()},
				{IbcSeqNum: 6, Data: testkeeper.GetNewSlashPacketData()},
				{IbcSeqNum: 5, Data: testkeeper.GetNewVSCMaturedPacketData()},
				{IbcSeqNum: 1, Data: testkeeper.GetNewVSCMaturedPacketData()},
			},
			expectedOrder:              []int{5, 4, 3, 2, 1, 0},
			toDelete:                   []int{1, 2, 3, 4, 5},
			expectedOrderAfterDeletion: []int{0},
		},
	}

	// Queue all packet data at once
	for _, chainData := range packetDataForMultipleConsumers {
		for _, dataInstance := range chainData.instances {
			providerKeeper.QueuePendingPacketData(ctx, chainData.chainID, dataInstance.IbcSeqNum, dataInstance.Data)
		}
	}

	// Assert retrieval ordering for each chain
	for _, chainData := range packetDataForMultipleConsumers {
		expectedInstances := getOrderedInstances(chainData.instances, chainData.expectedOrder)
		assertPendingPacketDataOrdering(t, &providerKeeper, ctx, chainData.chainID, expectedInstances)
	}

	// Delete specified data all at once
	for _, chainData := range packetDataForMultipleConsumers {
		for _, i := range chainData.toDelete {
			providerKeeper.DeletePendingPacketData(ctx, chainData.chainID, chainData.instances[i].IbcSeqNum)
		}
	}

	// Assert retrieval ordering after deletion for each chain
	for _, chainData := range packetDataForMultipleConsumers {
		expectedInstances := getOrderedInstances(chainData.instances, chainData.expectedOrderAfterDeletion)
		assertPendingPacketDataOrdering(t, &providerKeeper, ctx, chainData.chainID, expectedInstances)
	}
}

// TestDeletePendingPacketDataForConsumer tests the DeletePendingPacketDataForConsumer method.
func TestDeletePendingPacketDataForConsumer(t *testing.T) {

	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()
	providerKeeper.SetParams(ctx, providertypes.DefaultParams())

	// Queue slash and a VSC matured packet data for chain-48
	providerKeeper.QueuePendingSlashPacketData(ctx, "chain-48", 0, testkeeper.GetNewSlashPacketData())
	providerKeeper.QueuePendingVSCMaturedPacketData(ctx, "chain-48", 1, testkeeper.GetNewVSCMaturedPacketData())

	// Queue 3 slash, and 4 vsc matured packet data instances for chain-49
	providerKeeper.QueuePendingSlashPacketData(ctx, "chain-49", 0, testkeeper.GetNewSlashPacketData())
	providerKeeper.QueuePendingSlashPacketData(ctx, "chain-49", 1, testkeeper.GetNewSlashPacketData())
	providerKeeper.QueuePendingSlashPacketData(ctx, "chain-49", 2, testkeeper.GetNewSlashPacketData())
	providerKeeper.QueuePendingVSCMaturedPacketData(ctx, "chain-49", 3, testkeeper.GetNewVSCMaturedPacketData())
	providerKeeper.QueuePendingVSCMaturedPacketData(ctx, "chain-49", 4, testkeeper.GetNewVSCMaturedPacketData())
	providerKeeper.QueuePendingVSCMaturedPacketData(ctx, "chain-49", 5, testkeeper.GetNewVSCMaturedPacketData())
	providerKeeper.QueuePendingVSCMaturedPacketData(ctx, "chain-49", 6, testkeeper.GetNewVSCMaturedPacketData())

	// Delete all packet data for chain-49, confirm they are deleted
	providerKeeper.DeletePendingPacketDataForConsumer(ctx, "chain-49")
	slashData, vscMaturedData := providerKeeper.GetAllPendingPacketData(ctx, "chain-49")
	require.Empty(t, slashData)
	require.Empty(t, vscMaturedData)

	// Confirm packet data for chain-48 is not deleted
	slashData, vscMaturedData = providerKeeper.GetAllPendingPacketData(ctx, "chain-48")
	require.Len(t, slashData, 1)
	require.Len(t, vscMaturedData, 1)
}

// TestPanicIfTooMuchPendingPacketData tests the PanicIfTooMuchPendingPacketData method.
func TestPanicIfTooMuchPendingPacketData(t *testing.T) {

	testCases := []struct {
		max int64
	}{
		{max: 1},
		{max: 5},
		{max: 10},
		{max: 15},
		{max: 25},
	}

	for _, tc := range testCases {

		providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
		defer ctrl.Finish()

		// Set max pending slash packets param
		defaultParams := providertypes.DefaultParams()
		defaultParams.MaxPendingSlashPackets = tc.max
		providerKeeper.SetParams(ctx, defaultParams)

		rand.Seed(time.Now().UnixNano())

		// Queuing up a couple data instances for another chain shouldn't matter
		providerKeeper.QueuePendingPacketData(ctx, "chain-17", 0, testkeeper.GetNewSlashPacketData())
		providerKeeper.QueuePendingPacketData(ctx, "chain-17", 1, testkeeper.GetNewVSCMaturedPacketData())

		// Queue packet data instances until we reach the max (some slash packets, some VSC matured packets)
		reachedMax := false
		for i := 0; i < int(tc.max+2); i++ { // iterate up to tc.max+1
			randBool := rand.Intn(2) == 0
			var data interface{}
			if randBool {
				data = testkeeper.GetNewSlashPacketData()
			} else {
				data = testkeeper.GetNewVSCMaturedPacketData()
			}
			// Panic only if we've reached the max
			if i == int(tc.max+1) {
				require.Panics(t, func() {
					providerKeeper.QueuePendingPacketData(ctx, "chain-88", uint64(i), data)
				})
				reachedMax = true
			} else {
				providerKeeper.QueuePendingPacketData(ctx, "chain-88", uint64(i), data)
			}
		}
		require.True(t, reachedMax)
	}
}

// TestPendingPacketDataSize tests the getter, setter and incrementer for pending packet data size.
func TestPendingPacketDataSize(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// Confirm initial size is 0
	require.Equal(t, uint64(0), providerKeeper.GetPendingPacketDataSize(ctx, "chain-0"))

	// Set pending packet data size and confirm it was set
	providerKeeper.SetPendingPacketDataSize(ctx, "chain-0", 10)
	require.Equal(t, uint64(10), providerKeeper.GetPendingPacketDataSize(ctx, "chain-0"))

	// Increment pending packet data size and confirm it was incremented
	providerKeeper.IncrementPendingPacketDataSize(ctx, "chain-0")
	require.Equal(t, uint64(11), providerKeeper.GetPendingPacketDataSize(ctx, "chain-0"))
}

// TestSlashMeter tests the getter and setter for the slash gas meter
func TestSlashMeter(t *testing.T) {

	testCases := []struct {
		meterValue  sdktypes.Int
		shouldPanic bool
	}{
		{meterValue: sdktypes.NewInt(-7999999999999999999), shouldPanic: true},
		{meterValue: sdktypes.NewInt(-tmtypes.MaxTotalVotingPower - 1), shouldPanic: true},
		{meterValue: sdktypes.NewInt(-tmtypes.MaxTotalVotingPower), shouldPanic: false},
		{meterValue: sdktypes.NewInt(-50000000078987), shouldPanic: false},
		{meterValue: sdktypes.NewInt(-4237), shouldPanic: false},
		{meterValue: sdktypes.NewInt(0), shouldPanic: false},
		{meterValue: sdktypes.NewInt(1), shouldPanic: false},
		{meterValue: sdktypes.NewInt(4237897), shouldPanic: false},
		{meterValue: sdktypes.NewInt(500078078987), shouldPanic: false},
		{meterValue: sdktypes.NewInt(tmtypes.MaxTotalVotingPower), shouldPanic: false},
		{meterValue: sdktypes.NewInt(tmtypes.MaxTotalVotingPower + 1), shouldPanic: true},
		{meterValue: sdktypes.NewInt(7999974823991111199), shouldPanic: true},
	}

	for _, tc := range testCases {
		providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(
			t, testkeeper.NewInMemKeeperParams(t))
		defer ctrl.Finish()

		if tc.shouldPanic {
			require.Panics(t, func() {
				providerKeeper.SetSlashMeter(ctx, tc.meterValue)
			})
		} else {
			providerKeeper.SetSlashMeter(ctx, tc.meterValue)
			gotMeterValue := providerKeeper.GetSlashMeter(ctx)
			require.Equal(t, tc.meterValue, gotMeterValue)
		}
	}
}

// TestLastSlashMeterFullTime tests the getter and setter for the most recent time
// the slash meter was full.
func TestLastSlashMeterFullTime(t *testing.T) {

	testCases := []time.Time{
		time.Now(),
		time.Now().Add(1 * time.Hour).UTC(),
		time.Now().Add(2 * time.Hour).Local(),
		time.Now().Add(3 * time.Hour).In(time.FixedZone("UTC-8", -8*60*60)),
		time.Now().Add(4 * time.Hour).Local(),
		time.Now().Add(-1 * time.Hour).UTC(),
		time.Now().Add(-2 * time.Hour).Local(),
		time.Now().Add(-3 * time.Hour).UTC(),
		time.Now().Add(-4 * time.Hour).Local(),
	}

	for _, tc := range testCases {
		providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(
			t, testkeeper.NewInMemKeeperParams(t))
		defer ctrl.Finish()

		providerKeeper.SetLastSlashMeterFullTime(ctx, tc)
		gotTime := providerKeeper.GetLastSlashMeterFullTime(ctx)
		// Time should be returned in UTC
		require.Equal(t, tc.UTC(), gotTime)
	}
}

// Struct used for TestPendingPacketData and helpers
type pendingPacketDataInstance struct {
	IbcSeqNum uint64
	Data      interface{}
}

// getAllPendingPacketDataInstances returns all pending packet data instances in order from the pending packet data queue
func getAllPendingPacketDataInstances(ctx sdktypes.Context, k *keeper.Keeper, consumerChainId string) (instances []pendingPacketDataInstance) {
	k.IteratePendingPacketData(ctx, consumerChainId, func(ibcSeqNum uint64, data interface{}) bool {
		instances = append(instances, pendingPacketDataInstance{IbcSeqNum: ibcSeqNum, Data: data})
		return false
	})
	return
}

// getOrderedInstances returns the given instances in order, specified by the given indexes
func getOrderedInstances(instances []pendingPacketDataInstance, orderbyIdx []int) (orderedInstances []pendingPacketDataInstance) {
	toReturn := []pendingPacketDataInstance{}
	for _, idx := range orderbyIdx {
		toReturn = append(toReturn, instances[idx])
	}
	return toReturn
}

// Asserts that the pending packet data retrieved for this consumer chain matches what's expected
func assertPendingPacketDataOrdering(t *testing.T, k *keeper.Keeper, ctx sdktypes.Context,
	consumerChainId string, expectedInstances []pendingPacketDataInstance) {
	// Get all packet data for this chain
	obtainedInstances := getAllPendingPacketDataInstances(ctx, k, consumerChainId)
	// No extra data should be present
	require.Equal(t, len(expectedInstances), len(obtainedInstances))
	// Assert order and correct serialization/deserialization for each data instance
	for i, obtainedInstance := range obtainedInstances {
		require.Equal(t, expectedInstances[i], obtainedInstance)
	}
}
