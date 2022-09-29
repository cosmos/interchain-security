package keeper_test

import (
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
)

func TestPendingConsumerRemovalPropDeletion(t *testing.T) {

	testCases := []struct {
		types.ConsumerRemovalProposal
		ExpDeleted bool
	}{
		{
			ConsumerRemovalProposal: types.ConsumerRemovalProposal{ChainId: "8", StopTime: time.Now().UTC()},
			ExpDeleted:              true,
		},
		{
			ConsumerRemovalProposal: types.ConsumerRemovalProposal{ChainId: "9", StopTime: time.Now().UTC().Add(time.Hour)},
			ExpDeleted:              false,
		},
	}
	providerKeeper, ctx, ctrl := testkeeper.GetProviderKeeperAndCtx(t)
	defer ctrl.Finish()

	for _, tc := range testCases {
		providerKeeper.SetPendingConsumerRemovalProp(ctx, tc.ChainId, tc.StopTime)
	}

	ctx = ctx.WithBlockTime(time.Now().UTC())

	propsToExecute := providerKeeper.ConsumerRemovalPropsToExecute(ctx)
	// Delete consumer removal proposals, same as what would be done by IterateMatureConsumerRemovalProps
	providerKeeper.DeletePendingConsumerRemovalProps(ctx, propsToExecute...)
	numDeleted := 0
	for _, tc := range testCases {
		res := providerKeeper.GetPendingConsumerRemovalProp(ctx, tc.ChainId, tc.StopTime)
		if !tc.ExpDeleted {
			require.NotEmpty(t, res, "consumer removal prop was deleted: %s %s", tc.ChainId, tc.StopTime.String())
			continue
		}
		require.Empty(t, res, "consumer removal prop was not deleted %s %s", tc.ChainId, tc.StopTime.String())
		require.Equal(t, propsToExecute[numDeleted].ChainId, tc.ChainId)
		numDeleted += 1
	}
}

// Tests that pending consumer removal proposals are accessed in order by timestamp via the iterator
func TestPendingConsumerRemovalPropOrder(t *testing.T) {

	now := time.Now().UTC()

	// props with unique chain ids and spawn times
	sampleProp1 := types.ConsumerRemovalProposal{ChainId: "1", StopTime: now}
	sampleProp2 := types.ConsumerRemovalProposal{ChainId: "2", StopTime: now.Add(1 * time.Hour)}
	sampleProp3 := types.ConsumerRemovalProposal{ChainId: "3", StopTime: now.Add(2 * time.Hour)}
	sampleProp4 := types.ConsumerRemovalProposal{ChainId: "4", StopTime: now.Add(3 * time.Hour)}
	sampleProp5 := types.ConsumerRemovalProposal{ChainId: "5", StopTime: now.Add(4 * time.Hour)}

	testCases := []struct {
		propSubmitOrder      []types.ConsumerRemovalProposal
		accessTime           time.Time
		expectedOrderedProps []types.ConsumerRemovalProposal
	}{
		{
			propSubmitOrder: []types.ConsumerRemovalProposal{
				sampleProp1, sampleProp2, sampleProp3, sampleProp4, sampleProp5,
			},
			accessTime: now.Add(30 * time.Minute),
			expectedOrderedProps: []types.ConsumerRemovalProposal{
				sampleProp1,
			},
		},
		{
			propSubmitOrder: []types.ConsumerRemovalProposal{
				sampleProp3, sampleProp2, sampleProp1, sampleProp5, sampleProp4,
			},
			accessTime: now.Add(3 * time.Hour).Add(30 * time.Minute),
			expectedOrderedProps: []types.ConsumerRemovalProposal{
				sampleProp1, sampleProp2, sampleProp3, sampleProp4,
			},
		},
		{
			propSubmitOrder: []types.ConsumerRemovalProposal{
				sampleProp5, sampleProp4, sampleProp3, sampleProp2, sampleProp1,
			},
			accessTime: now.Add(5 * time.Hour),
			expectedOrderedProps: []types.ConsumerRemovalProposal{
				sampleProp1, sampleProp2, sampleProp3, sampleProp4, sampleProp5,
			},
		},
	}

	for _, tc := range testCases {
		providerKeeper, ctx, ctrl := testkeeper.GetProviderKeeperAndCtx(t)
		defer ctrl.Finish()
		ctx = ctx.WithBlockTime(tc.accessTime)

		for _, prop := range tc.propSubmitOrder {
			providerKeeper.SetPendingConsumerRemovalProp(ctx, prop.ChainId, prop.StopTime)
		}
		propsToExecute := providerKeeper.ConsumerRemovalPropsToExecute(ctx)
		require.Equal(t, tc.expectedOrderedProps, propsToExecute)
	}
}

func TestPendingConsumerAdditionPropDeletion(t *testing.T) {

	testCases := []struct {
		types.ConsumerAdditionProposal
		ExpDeleted bool
	}{
		{
			ConsumerAdditionProposal: types.ConsumerAdditionProposal{ChainId: "0", SpawnTime: time.Now().UTC()},
			ExpDeleted:               true,
		},
		{
			ConsumerAdditionProposal: types.ConsumerAdditionProposal{ChainId: "1", SpawnTime: time.Now().UTC().Add(time.Hour)},
			ExpDeleted:               false,
		},
	}
	providerKeeper, ctx, ctrl := testkeeper.GetProviderKeeperAndCtx(t)
	defer ctrl.Finish()

	for _, tc := range testCases {
		err := providerKeeper.SetPendingConsumerAdditionProp(ctx, &tc.ConsumerAdditionProposal)
		require.NoError(t, err)
	}

	ctx = ctx.WithBlockTime(time.Now().UTC())

	propsToExecute := providerKeeper.ConsumerAdditionPropsToExecute(ctx)
	// Delete consumer addition proposals, same as what would be done by IterateMatureConsumerAdditionProps
	providerKeeper.DeletePendingConsumerAdditionProps(ctx, propsToExecute...)
	numDeleted := 0
	for _, tc := range testCases {
		res := providerKeeper.GetPendingConsumerAdditionProp(ctx, tc.SpawnTime, tc.ChainId)
		if !tc.ExpDeleted {
			require.NotEmpty(t, res, "consumer addition proposal was deleted: %s %s", tc.ChainId, tc.SpawnTime.String())
			continue
		}
		require.Empty(t, res, "consumer addition proposal was not deleted %s %s", tc.ChainId, tc.SpawnTime.String())
		require.Equal(t, propsToExecute[numDeleted].ChainId, tc.ChainId)
		numDeleted += 1
	}
}

// Tests that pending consumer addition proposals are accessed in order by timestamp via the iterator
func TestPendingConsumerAdditionPropOrder(t *testing.T) {

	now := time.Now().UTC()

	// props with unique chain ids and spawn times
	sampleProp1 := types.ConsumerAdditionProposal{ChainId: "1", SpawnTime: now}
	sampleProp2 := types.ConsumerAdditionProposal{ChainId: "2", SpawnTime: now.Add(1 * time.Hour)}
	sampleProp3 := types.ConsumerAdditionProposal{ChainId: "3", SpawnTime: now.Add(2 * time.Hour)}
	sampleProp4 := types.ConsumerAdditionProposal{ChainId: "4", SpawnTime: now.Add(3 * time.Hour)}
	sampleProp5 := types.ConsumerAdditionProposal{ChainId: "5", SpawnTime: now.Add(4 * time.Hour)}

	testCases := []struct {
		propSubmitOrder      []types.ConsumerAdditionProposal
		accessTime           time.Time
		expectedOrderedProps []types.ConsumerAdditionProposal
	}{
		{
			propSubmitOrder: []types.ConsumerAdditionProposal{
				sampleProp1, sampleProp2, sampleProp3, sampleProp4, sampleProp5,
			},
			accessTime: now.Add(30 * time.Minute),
			expectedOrderedProps: []types.ConsumerAdditionProposal{
				sampleProp1,
			},
		},
		{
			propSubmitOrder: []types.ConsumerAdditionProposal{
				sampleProp3, sampleProp2, sampleProp1, sampleProp5, sampleProp4,
			},
			accessTime: now.Add(3 * time.Hour).Add(30 * time.Minute),
			expectedOrderedProps: []types.ConsumerAdditionProposal{
				sampleProp1, sampleProp2, sampleProp3, sampleProp4,
			},
		},
		{
			propSubmitOrder: []types.ConsumerAdditionProposal{
				sampleProp5, sampleProp4, sampleProp3, sampleProp2, sampleProp1,
			},
			accessTime: now.Add(5 * time.Hour),
			expectedOrderedProps: []types.ConsumerAdditionProposal{
				sampleProp1, sampleProp2, sampleProp3, sampleProp4, sampleProp5,
			},
		},
	}

	for _, tc := range testCases {
		providerKeeper, ctx, ctrl := testkeeper.GetProviderKeeperAndCtx(t)
		defer ctrl.Finish()

		ctx = ctx.WithBlockTime(tc.accessTime)

		for _, prop := range tc.propSubmitOrder {
			err := providerKeeper.SetPendingConsumerAdditionProp(ctx, &prop)
			require.NoError(t, err)
		}
		propsToExecute := providerKeeper.ConsumerAdditionPropsToExecute(ctx)
		require.Equal(t, tc.expectedOrderedProps, propsToExecute)
	}
}
