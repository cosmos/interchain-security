package keeper_test

import (
	testkeeper "github.com/cosmos/interchain-security/v5/testutil/keeper"
	"github.com/stretchr/testify/require"
	"testing"
)

// TestConsumerId tests methods for retrieving and incrementing consumer id
func TestConsumerId(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerId, found := providerKeeper.GetConsumerId(ctx)
	require.False(t, found)

	consumerId = providerKeeper.FetchAndIncrementConsumerId(ctx)
	require.Equal(t, uint64(0), consumerId)

	consumerId, found = providerKeeper.GetConsumerId(ctx)
	require.True(t, found)
	require.Equal(t, uint64(1), consumerId)

	consumerId = providerKeeper.FetchAndIncrementConsumerId(ctx)
	require.Equal(t, uint64(1), consumerId)

	consumerId, found = providerKeeper.GetConsumerId(ctx)
	require.True(t, found)
	require.Equal(t, uint64(2), consumerId)
}

// TestConsumerIdToChainId tests the getter, setter, and deletion methods for the consumer id to chain id
func TestConsumerIdToChainId(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	_, found := providerKeeper.GetConsumerIdToChainId(ctx, "consumerId")
	require.False(t, found)

	providerKeeper.SetConsumerIdToChainId(ctx, "consumerId", "chainId")
	chainId, found := providerKeeper.GetConsumerIdToChainId(ctx, "consumerId")
	require.True(t, found)
	require.Equal(t, "chainId", chainId)

	providerKeeper.SetConsumerIdToChainId(ctx, "consumerId", "chainId2")
	chainId, found = providerKeeper.GetConsumerIdToChainId(ctx, "consumerId")
	require.True(t, found)
	require.Equal(t, "chainId2", chainId)

	providerKeeper.DeleteConsumerIdToChainId(ctx, "consumerId")
	chainId, found = providerKeeper.GetConsumerIdToChainId(ctx, "consumerId")
	require.False(t, found)
	require.Equal(t, "", chainId)
}

// TestClientIdToConsumerId tests the getter, setter, and deletion methods for the client id to consumer id
func TestClientIdToConsumerId(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	_, found := providerKeeper.GetClientIdToConsumerId(ctx, "clientId")
	require.False(t, found)

	providerKeeper.SetClientIdToConsumerId(ctx, "clientId", "consumerId")
	consumerId, found := providerKeeper.GetClientIdToConsumerId(ctx, "clientId")
	require.True(t, found)
	require.Equal(t, "consumerId", consumerId)

	providerKeeper.SetClientIdToConsumerId(ctx, "clientId", "consumerId2")
	consumerId, found = providerKeeper.GetClientIdToConsumerId(ctx, "clientId")
	require.True(t, found)
	require.Equal(t, "consumerId2", consumerId)

	providerKeeper.DeleteClientIdToConsumerId(ctx, "clientId")
	consumerId, found = providerKeeper.GetClientIdToConsumerId(ctx, "clientId")
	require.False(t, found)
	require.Equal(t, "", consumerId)
}
