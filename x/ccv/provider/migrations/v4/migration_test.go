package v4

import (
	"testing"

	"github.com/stretchr/testify/require"

	testutil "github.com/cosmos/interchain-security/v5/testutil/keeper"
	providertypes "github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
)

func TestMigrateParams(t *testing.T) {
	inMemParams := testutil.NewInMemKeeperParams(t)
	_, ctx, ctrl, _ := testutil.GetProviderKeeperAndCtx(t, inMemParams)
	defer ctrl.Finish()

	// initially blocks per epoch param does not exist
	require.False(t, inMemParams.ParamsSubspace.Has(ctx, providertypes.KeyBlocksPerEpoch))

	MigrateParams(ctx, *inMemParams.ParamsSubspace)

	// after migration, blocks per epoch param should exist and be equal to default
	require.True(t, inMemParams.ParamsSubspace.Has(ctx, providertypes.KeyBlocksPerEpoch))
	var blocksPerEpochParam int64
	inMemParams.ParamsSubspace.Get(ctx, providertypes.KeyBlocksPerEpoch, &blocksPerEpochParam)
	require.Equal(t, providertypes.DefaultBlocksPerEpoch, blocksPerEpochParam)
}
