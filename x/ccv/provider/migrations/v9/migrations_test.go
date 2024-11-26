package v9

import (
	"testing"

	"github.com/stretchr/testify/require"

	testutil "github.com/cosmos/interchain-security/v6/testutil/keeper"
)

func TestSetDefaultConsumerInfractionParams(t *testing.T) {
	t.Helper()
	inMemParams := testutil.NewInMemKeeperParams(t)
	k, ctx, ctrl, _ := testutil.GetProviderKeeperAndCtx(t, inMemParams)
	defer ctrl.Finish()

	store := ctx.KVStore(inMemParams.StoreKey)

	activeConsumerIds := k.GetAllActiveConsumerIds(ctx)

	for _, consumerId := range activeConsumerIds {
		_, err := k.GetInfractionParameters(ctx, consumerId)
		require.Error(t, err)
	}

	err := MigrateConsumerInfractionParams(ctx, store, k)
	require.NoError(t, err)

	defaultInfractionParams := defaultInfractionParams()
	for _, consumerId := range activeConsumerIds {
		infractionParams, err := k.GetInfractionParameters(ctx, consumerId)
		require.NoError(t, err)
		require.Equal(t, defaultInfractionParams, infractionParams)
	}
}
