package keeper_test

import (
	"testing"
	"time"

	"cosmossdk.io/math"
	testkeeper "github.com/cosmos/interchain-security/v7/testutil/keeper"
	providertypes "github.com/cosmos/interchain-security/v7/x/ccv/provider/types"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"
)

func TestUpdateQueuedInfractionParams_RemoveIdenticalItem(t *testing.T) {
	k, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerID := "consumer1"
	initialParams := providertypes.InfractionParameters{
		DoubleSign: &providertypes.SlashJailParameters{
			JailDuration:  1000 * time.Second,
			SlashFraction: math.LegacyNewDecWithPrec(4, 1),
		},
		Downtime: &providertypes.SlashJailParameters{
			JailDuration:  500 * time.Second,
			SlashFraction: math.LegacyNewDec(0),
		},
	}

	// Set initial infraction parameters
	require.NoError(t, k.SetInfractionParameters(ctx, consumerID, initialParams))

	// Queue identical parameters
	require.NoError(t, k.UpdateQueuedInfractionParams(ctx, consumerID, initialParams))

	// Verify queue is empty
	hasQueued := k.HasQueuedInfractionParameters(ctx, consumerID)
	require.False(t, hasQueued)
}

func TestUpdateQueuedInfractionParams_UpdateDifferentItem(t *testing.T) {
	k, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	mocks.MockStakingKeeper.EXPECT().UnbondingTime(ctx).Return(time.Second, nil).AnyTimes()

	consumerID := "consumer2"
	initialParams := providertypes.InfractionParameters{
		DoubleSign: &providertypes.SlashJailParameters{
			JailDuration:  1000 * time.Second,
			SlashFraction: math.LegacyNewDecWithPrec(4, 1),
		},
		Downtime: &providertypes.SlashJailParameters{
			JailDuration:  500 * time.Second,
			SlashFraction: math.LegacyNewDec(0),
		},
	}
	newParams := providertypes.InfractionParameters{
		DoubleSign: &providertypes.SlashJailParameters{
			JailDuration:  2000 * time.Second,
			SlashFraction: math.LegacyNewDecWithPrec(5, 1),
		},
		Downtime: &providertypes.SlashJailParameters{
			JailDuration:  1000 * time.Second,
			SlashFraction: math.LegacyNewDec(1),
		},
	}

	// Set initial infraction parameters
	require.NoError(t, k.SetInfractionParameters(ctx, consumerID, initialParams))

	// Queue different parameters
	require.NoError(t, k.UpdateQueuedInfractionParams(ctx, consumerID, newParams))

	// Verify queue has updated parameters
	queuedParams, err := k.GetQueuedInfractionParameters(ctx, consumerID)
	require.NoError(t, err)
	require.Equal(t, newParams, queuedParams)
}

func TestUpdateQueuedInfractionParams_OnlyLastItemInQueue(t *testing.T) {
	k, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	mocks.MockStakingKeeper.EXPECT().UnbondingTime(ctx).Return(time.Second, nil).AnyTimes()

	initialParams := providertypes.InfractionParameters{
		DoubleSign: &providertypes.SlashJailParameters{
			JailDuration:  1000 * time.Second,
			SlashFraction: math.LegacyNewDecWithPrec(4, 1),
		},
		Downtime: &providertypes.SlashJailParameters{
			JailDuration:  500 * time.Second,
			SlashFraction: math.LegacyNewDec(0),
		},
	}

	consumerID := "consumer3"
	paramsList := []providertypes.InfractionParameters{
		{
			DoubleSign: &providertypes.SlashJailParameters{
				JailDuration:  1000 * time.Second,
				SlashFraction: math.LegacyNewDecWithPrec(4, 1),
			},
			Downtime: &providertypes.SlashJailParameters{
				JailDuration:  500 * time.Second,
				SlashFraction: math.LegacyNewDec(0),
			},
		},
		{
			DoubleSign: &providertypes.SlashJailParameters{
				JailDuration:  1500 * time.Second,
				SlashFraction: math.LegacyNewDecWithPrec(3, 1),
			},
			Downtime: &providertypes.SlashJailParameters{
				JailDuration:  600 * time.Second,
				SlashFraction: math.LegacyNewDec(0),
			},
		},
	}

	// Set initial infraction parameters
	require.NoError(t, k.SetInfractionParameters(ctx, consumerID, initialParams))

	// Queue multiple parameters
	for _, params := range paramsList {
		require.NoError(t, k.UpdateQueuedInfractionParams(ctx, consumerID, params))
	}

	// Verify only the last one is kept in the queue
	queuedParams, err := k.GetQueuedInfractionParameters(ctx, consumerID)
	require.NoError(t, err)
	require.Equal(t, paramsList[len(paramsList)-1], queuedParams)
}

func TestBeginBlockUpdateInfractionParameters_MixedTiming(t *testing.T) {
	keeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	unbondingTime := time.Second
	mocks.MockStakingKeeper.EXPECT().UnbondingTime(gomock.Any()).Return(unbondingTime, nil).AnyTimes()

	// Define old and new InfractionParameters
	oldInfractionParams := providertypes.InfractionParameters{
		DoubleSign: &providertypes.SlashJailParameters{
			JailDuration:  1000 * time.Second,
			SlashFraction: math.LegacyNewDecWithPrec(4, 1), // 0.4
		},
		Downtime: &providertypes.SlashJailParameters{
			JailDuration:  500 * time.Second,
			SlashFraction: math.LegacyNewDec(0),
		},
	}
	newInfractionParams := providertypes.InfractionParameters{
		DoubleSign: &providertypes.SlashJailParameters{
			JailDuration:  1200 * time.Second,
			SlashFraction: math.LegacyNewDecWithPrec(5, 1), // 0.5
		},
		Downtime: &providertypes.SlashJailParameters{
			JailDuration:  600 * time.Second,
			SlashFraction: math.LegacyNewDecWithPrec(1, 1), // 0.1
		},
	}

	// Define consumers
	consumerIds := []string{"consumer1", "consumer2", "consumer3", "consumer4"}

	// Set old infraction parameters for all consumers
	for _, consumerId := range consumerIds {
		err := keeper.SetInfractionParameters(ctx, consumerId, oldInfractionParams)
		require.NoError(t, err)
	}

	// Create contexts for different time scenarios
	currentTime := ctx.BlockTime()
	ctxWithTimeBefore := ctx.WithBlockTime(currentTime.Add(-2 * unbondingTime))
	ctxWithTimeAfter := ctx.WithBlockTime(currentTime.Add(2 * unbondingTime))

	// Queue updates for consumers
	err := keeper.UpdateQueuedInfractionParams(ctxWithTimeBefore, "consumer1", newInfractionParams)
	require.NoError(t, err)
	err = keeper.UpdateQueuedInfractionParams(ctxWithTimeBefore, "consumer2", newInfractionParams)
	require.NoError(t, err)
	err = keeper.UpdateQueuedInfractionParams(ctxWithTimeAfter, "consumer3", newInfractionParams)
	require.NoError(t, err)
	err = keeper.UpdateQueuedInfractionParams(ctxWithTimeAfter, "consumer4", newInfractionParams)
	require.NoError(t, err)

	// Call BeginBlockUpdateInfractionParameters with current context
	err = keeper.BeginBlockUpdateInfractionParameters(ctx)
	require.NoError(t, err)

	// Confirm queue state
	require.True(t, keeper.HasQueuedInfractionParameters(ctx, "consumer3"))
	require.True(t, keeper.HasQueuedInfractionParameters(ctx, "consumer4"))
	require.False(t, keeper.HasQueuedInfractionParameters(ctx, "consumer1"))
	require.False(t, keeper.HasQueuedInfractionParameters(ctx, "consumer2"))

	// Confirm infraction parameters are updated for consumer1 and consumer2
	params1, err := keeper.GetInfractionParameters(ctx, "consumer1")
	require.NoError(t, err)
	require.Equal(t, params1, newInfractionParams)

	params2, err := keeper.GetInfractionParameters(ctx, "consumer2")
	require.NoError(t, err)
	require.Equal(t, params2, newInfractionParams)

	// Confirm infraction parameters are not updated for consumer3 and consumer4
	params3, err := keeper.GetInfractionParameters(ctx, "consumer3")
	require.NoError(t, err)
	require.Equal(t, params3, oldInfractionParams)

	params4, err := keeper.GetInfractionParameters(ctx, "consumer4")
	require.NoError(t, err)
	require.Equal(t, params4, oldInfractionParams)
}
