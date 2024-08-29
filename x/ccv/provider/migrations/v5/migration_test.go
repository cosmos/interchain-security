package v5

import (
	"testing"

	"github.com/stretchr/testify/require"

	testutil "github.com/cosmos/interchain-security/v5/testutil/keeper"
)

func TestMigrateParams(t *testing.T) {
	inMemParams := testutil.NewInMemKeeperParams(t)
	provKeeper, ctx, ctrl, _ := testutil.GetProviderKeeperAndCtx(t, inMemParams)
	defer ctrl.Finish()

	provKeeper.SetConsumerClientId(ctx, "chainID", "clientID")

	// initially top N should not exist
	topN, err := provKeeper.GetTopN(ctx, "chainID")
	require.NoError(t, err)
	require.Zero(t, topN)

	// migrate
	MigrateTopNForRegisteredChains(ctx, provKeeper)

	// after migration, top N should be 95
	topN, err = provKeeper.GetTopN(ctx, "chainID")
	require.NoError(t, err)
	require.Equal(t, uint32(95), topN)
}
