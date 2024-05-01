package vPSS

import (
	"testing"

	"github.com/stretchr/testify/require"

	testutil "github.com/cosmos/interchain-security/v4/testutil/keeper"
)

func TestMigrateParams(t *testing.T) {
	inMemParams := testutil.NewInMemKeeperParams(t)
	provKeeper, ctx, ctrl, _ := testutil.GetProviderKeeperAndCtx(t, inMemParams)
	defer ctrl.Finish()

	provKeeper.SetConsumerClientId(ctx, "chainID", "clientID")

	// initially top N should not exist
	topN, found := provKeeper.GetTopN(ctx, "chainID")
	require.False(t, found)
	require.Zero(t, topN)

	// migrate
	MigrateTopNForRegisteredChains(ctx, provKeeper)

	// after migration, top N should be 95
	topN, found = provKeeper.GetTopN(ctx, "chainID")
	require.True(t, found)
	require.Equal(t, uint32(95), topN)
}
