package keeper_test

import (
	"testing"
	"time"

	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"

	"cosmossdk.io/math"

	sdktypes "github.com/cosmos/cosmos-sdk/types"

	tmtypes "github.com/cometbft/cometbft/types"

	testkeeper "github.com/cosmos/interchain-security/v5/testutil/keeper"
	providertypes "github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
)

// TestSlashMeterReplenishment tests the CheckForSlashMeterReplenishment, ReplenishSlashMeter,
// and InitializeSlashMeter methods.
func TestSlashMeterReplenishment(t *testing.T) {
	testCases := []struct {
		replenishPeriod   time.Duration
		replenishFraction string
		totalPower        math.Int
		// Replenish fraction * total power, also serves as max slash meter value
		expectedAllowance math.Int
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

		now := time.Now().UTC()
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

		// Confirm replenish time candidate is set to now + replenish period
		initialReplenishCandidate := providerKeeper.GetSlashMeterReplenishTimeCandidate(ctx)
		require.Equal(t, now.Add(tc.replenishPeriod), initialReplenishCandidate)

		// Decrement slash meter
		providerKeeper.SetSlashMeter(ctx, providerKeeper.GetSlashMeter(ctx).Sub(sdktypes.NewInt(3)))
		require.Equal(t, tc.expectedAllowance.Sub(sdktypes.NewInt(3)), providerKeeper.GetSlashMeter(ctx))

		// Check for replenishment, confirm meter is not replenished (since no time has passed since init)
		meterBefore := providerKeeper.GetSlashMeter(ctx)
		providerKeeper.CheckForSlashMeterReplenishment(ctx)
		require.Equal(t, meterBefore, providerKeeper.GetSlashMeter(ctx))

		// Confirm replenishment time candidate is not updated
		require.Equal(t, initialReplenishCandidate, providerKeeper.GetSlashMeterReplenishTimeCandidate(ctx))

		// Note: odd time formats are used as an extra sanity check that UTC format is persisted

		// Increment block time by half replenish period
		ctx = ctx.WithBlockTime(now.Add(tc.replenishPeriod / 2).Local())

		// Confirm meter is not still not replenished
		meterBefore = providerKeeper.GetSlashMeter(ctx)
		providerKeeper.CheckForSlashMeterReplenishment(ctx)
		require.Equal(t, meterBefore, providerKeeper.GetSlashMeter(ctx))

		// Confirm replenishment time candidate is not updated
		require.Equal(t, initialReplenishCandidate, providerKeeper.GetSlashMeterReplenishTimeCandidate(ctx))

		// Increment block time by more than replenish period
		ctx = ctx.WithBlockTime(now.Add(tc.replenishPeriod * 2).In(time.FixedZone("UTC-8", -8*60*60)))

		// Confirm meter is now replenished to max value
		providerKeeper.CheckForSlashMeterReplenishment(ctx)
		require.Equal(t, tc.expectedAllowance, providerKeeper.GetSlashMeter(ctx))

		// Replenish time candidate should be updated to block time + replenish period
		require.NotEqual(t, initialReplenishCandidate, providerKeeper.GetSlashMeterReplenishTimeCandidate(ctx))
		require.Equal(t, ctx.BlockTime().Add(tc.replenishPeriod), providerKeeper.GetSlashMeterReplenishTimeCandidate(ctx))

		// increment block time by more than replenish period again
		ctx = ctx.WithBlockTime(ctx.BlockTime().Add(tc.replenishPeriod * 2))

		// Confirm that meter is capped at max value
		providerKeeper.CheckForSlashMeterReplenishment(ctx)
		require.Equal(t, tc.expectedAllowance, providerKeeper.GetSlashMeter(ctx))

		// Confirm replenish candidate is updated, even though meter was not replenished
		require.Equal(t, ctx.BlockTime().Add(tc.replenishPeriod), providerKeeper.GetSlashMeterReplenishTimeCandidate(ctx))
	}
}

// Tests that the slash meter exhibits desired behavior when multiple replenishments are needed
// to restore it to a full value.
func TestConsecutiveReplenishments(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(
		t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	now := time.Now().UTC()
	ctx = ctx.WithBlockTime(now)

	// Set desired params
	params := providertypes.DefaultParams()
	params.SlashMeterReplenishPeriod = time.Hour
	params.SlashMeterReplenishFraction = "0.05"
	providerKeeper.SetParams(ctx, params)

	// Mock total power from staking keeper using test case value
	// Any ctx is accepted, and the method will be called multiple times during the tests
	gomock.InOrder(
		mocks.MockStakingKeeper.EXPECT().GetLastTotalPower(
			gomock.Any()).Return(sdktypes.NewInt(1000)).AnyTimes(),
	)

	// Now we can initialize the slash meter (this would happen in InitGenesis)
	providerKeeper.InitializeSlashMeter(ctx)

	// Confirm meter value is initialized to expected allowance
	require.Equal(t, int64(50), providerKeeper.GetSlashMeter(ctx).Int64())

	// Confirm replenish candidate is set to now + replenish period
	require.Equal(t, now.Add(time.Hour), providerKeeper.GetSlashMeterReplenishTimeCandidate(ctx))

	// Decrement slash meter to negative value that would take 4 replenishments to recover from
	providerKeeper.SetSlashMeter(ctx, sdktypes.NewInt(-150))

	// Confirm no replenishment occurs when no time has passed, replenish candidate is not updated
	providerKeeper.CheckForSlashMeterReplenishment(ctx)
	require.Equal(t, sdktypes.NewInt(-150), providerKeeper.GetSlashMeter(ctx))
	require.Equal(t, now.Add(time.Hour), providerKeeper.GetSlashMeterReplenishTimeCandidate(ctx))

	// Now increment block time past replenishment period and confirm that meter is replenished ONCE,
	// and replenish candidate is updated to block time + replenish period
	ctx = ctx.WithBlockTime(ctx.BlockTime().Add(2 * time.Hour))
	providerKeeper.CheckForSlashMeterReplenishment(ctx)
	require.Equal(t, sdktypes.NewInt(-100), providerKeeper.GetSlashMeter(ctx))
	require.Equal(t, now.Add(3*time.Hour), providerKeeper.GetSlashMeterReplenishTimeCandidate(ctx)) // Note 3 hours, not 2

	// Simulate next block and check that no consecutive replenishments occur (replenish period has not passed)
	// and replenish candidate is not updated
	ctx = ctx.WithBlockTime(ctx.BlockTime().Add(5 * time.Second))
	providerKeeper.CheckForSlashMeterReplenishment(ctx)
	require.Equal(t, sdktypes.NewInt(-100), providerKeeper.GetSlashMeter(ctx))
	require.Equal(t, now.Add(3*time.Hour), providerKeeper.GetSlashMeterReplenishTimeCandidate(ctx))

	// Increment block time past replenishment period and confirm that meter is replenished ONCE more
	// and replenish candidate is updated to block time + replenish period
	ctx = ctx.WithBlockTime(ctx.BlockTime().Add(time.Hour * 1))
	providerKeeper.CheckForSlashMeterReplenishment(ctx)
	require.Equal(t, sdktypes.NewInt(-50), providerKeeper.GetSlashMeter(ctx))
	require.Equal(t, now.Add(4*time.Hour).Add(5*time.Second), providerKeeper.GetSlashMeterReplenishTimeCandidate(ctx))

	// Replenishments should happen if we increment block times past replenishment period
	ctx = ctx.WithBlockTime(ctx.BlockTime().Add(time.Hour * 1))
	providerKeeper.CheckForSlashMeterReplenishment(ctx)
	require.Equal(t, sdktypes.NewInt(0), providerKeeper.GetSlashMeter(ctx))
	require.Equal(t, now.Add(5*time.Hour).Add(5*time.Second), providerKeeper.GetSlashMeterReplenishTimeCandidate(ctx))
	providerKeeper.CheckForSlashMeterReplenishment(ctx)
	require.Equal(t, sdktypes.NewInt(0), providerKeeper.GetSlashMeter(ctx))
	require.Equal(t, now.Add(5*time.Hour).Add(5*time.Second), providerKeeper.GetSlashMeterReplenishTimeCandidate(ctx))
	ctx = ctx.WithBlockTime(ctx.BlockTime().Add(time.Hour * 1))
	providerKeeper.CheckForSlashMeterReplenishment(ctx)
	require.Equal(t, sdktypes.NewInt(50), providerKeeper.GetSlashMeter(ctx))
	require.Equal(t, now.Add(6*time.Hour).Add(5*time.Second), providerKeeper.GetSlashMeterReplenishTimeCandidate(ctx))
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
		slashedPower           math.Int
		totalPower             math.Int
		replenishFraction      string
		numReplenishesTillFull int
		finalMeterValue        math.Int
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
		totalPower        math.Int
		// Replenish fraction * total power
		expectedAllowance math.Int
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

// TestSlashMeter tests the getter and setter for the slash gas meter
func TestSlashMeter(t *testing.T) {
	testCases := []struct {
		meterValue  math.Int
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

// TestSlashMeterReplenishTimeCandidate tests the getter and setter for the slash meter replenish time candidate
func TestSlashMeterReplenishTimeCandidate(t *testing.T) {
	testCases := []struct {
		blockTime       time.Time
		replenishPeriod time.Duration
	}{
		{time.Now(), time.Hour},
		{time.Now().Add(1 * time.Hour).UTC(), time.Hour},
		{time.Now().Add(2 * time.Hour).Local(), 5 * time.Hour},
		{time.Now().Add(3 * time.Hour).In(time.FixedZone("UTC-8", -8*60*60)), 10 * time.Hour},
		{time.Now().Add(4 * time.Hour).Local(), 15 * time.Minute},
		{time.Now().Add(-1 * time.Hour).UTC(), time.Minute},
		{time.Now().Add(-2 * time.Hour).Local(), 2 * time.Minute},
		{time.Now().Add(-3 * time.Hour).UTC(), 3 * time.Minute},
		{time.Now().Add(-4 * time.Hour).Local(), 4 * time.Minute},
	}

	for _, tc := range testCases {
		providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(
			t, testkeeper.NewInMemKeeperParams(t))
		defer ctrl.Finish()

		ctx = ctx.WithBlockTime(tc.blockTime)
		params := providertypes.DefaultParams()
		params.SlashMeterReplenishPeriod = tc.replenishPeriod
		providerKeeper.SetParams(ctx, params)

		providerKeeper.SetSlashMeterReplenishTimeCandidate(ctx)
		gotTime := providerKeeper.GetSlashMeterReplenishTimeCandidate(ctx)

		// Time should be returned in UTC
		require.Equal(t, tc.blockTime.Add(tc.replenishPeriod).UTC(), gotTime)
	}
}
