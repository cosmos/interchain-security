package keeper_test

import (
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
)

func TestPendingStopProposalDeletion(t *testing.T) {

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
	providerKeeper, ctx := testkeeper.GetProviderKeeperAndCtx(t)

	for _, tc := range testCases {
		providerKeeper.SetPendingStopProposal(ctx, tc.ChainId, tc.StopTime)
	}

	ctx = ctx.WithBlockTime(time.Now().UTC())

	propsToExecute := providerKeeper.StopProposalsToExecute(ctx)
	// Delete stop proposals, same as what would be done by IteratePendingStopProposal
	providerKeeper.DeletePendingStopProposals(ctx, propsToExecute...)
	numDeleted := 0
	for _, tc := range testCases {
		res := providerKeeper.GetPendingStopProposal(ctx, tc.ChainId, tc.StopTime)
		if !tc.ExpDeleted {
			require.NotEmpty(t, res, "stop proposal was deleted: %s %s", tc.ChainId, tc.StopTime.String())
			continue
		}
		require.Empty(t, res, "stop proposal was not deleted %s %s", tc.ChainId, tc.StopTime.String())
		require.Equal(t, propsToExecute[numDeleted].ChainId, tc.ChainId)
		numDeleted += 1
	}
}

// Tests that pending stop proposals are accessed in order by timestamp via the iterator
func TestPendingStopProposalsOrder(t *testing.T) {

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
		providerKeeper, ctx := testkeeper.GetProviderKeeperAndCtx(t)
		ctx = ctx.WithBlockTime(tc.accessTime)

		for _, prop := range tc.propSubmitOrder {
			providerKeeper.SetPendingStopProposal(ctx, prop.ChainId, prop.StopTime)
		}
		propsToExecute := providerKeeper.StopProposalsToExecute(ctx)
		require.Equal(t, tc.expectedOrderedProps, propsToExecute)
	}
}

func TestPendingCreateProposalsDeletion(t *testing.T) {

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
	providerKeeper, ctx := testkeeper.GetProviderKeeperAndCtx(t)

	for _, tc := range testCases {
		err := providerKeeper.SetPendingConsumerAdditionProp(ctx, &tc.ConsumerAdditionProposal)
		require.NoError(t, err)
	}

	ctx = ctx.WithBlockTime(time.Now().UTC())

	propsToExecute := providerKeeper.ConsumerAdditionPropsToExecute(ctx)
	// Delete consumer addition proposals, same as what would be done by IteratePendingConsumerAdditionProps
	providerKeeper.DeletePendingConsumerAdditionProps(ctx, propsToExecute...)
	numDeleted := 0
	for _, tc := range testCases {
		res := providerKeeper.GetPendingConsumerAdditionProp(ctx, tc.SpawnTime, tc.ChainId)
		if !tc.ExpDeleted {
			require.NotEmpty(t, res, "create proposal was deleted: %s %s", tc.ChainId, tc.SpawnTime.String())
			continue
		}
		require.Empty(t, res, "create proposal was not deleted %s %s", tc.ChainId, tc.SpawnTime.String())
		require.Equal(t, propsToExecute[numDeleted].ChainId, tc.ChainId)
		numDeleted += 1
	}
}

// Tests that pending create proposals are accessed in order by timestamp via the iterator
func TestPendingCreateProposalsOrder(t *testing.T) {

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
		providerKeeper, ctx := testkeeper.GetProviderKeeperAndCtx(t)
		ctx = ctx.WithBlockTime(tc.accessTime)

		for _, prop := range tc.propSubmitOrder {
			err := providerKeeper.SetPendingConsumerAdditionProp(ctx, &prop)
			require.NoError(t, err)
		}
		propsToExecute := providerKeeper.ConsumerAdditionPropsToExecute(ctx)
		require.Equal(t, tc.expectedOrderedProps, propsToExecute)
	}
}
