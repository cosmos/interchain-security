package v6

import (
	"testing"

	"github.com/stretchr/testify/require"

	testutil "github.com/cosmos/interchain-security/v4/testutil/keeper"
	providertypes "github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
)

func TestMigrateParams(t *testing.T) {
	inMemParams := testutil.NewInMemKeeperParams(t)
	_, ctx, ctrl, _ := testutil.GetProviderKeeperAndCtx(t, inMemParams)
	defer ctrl.Finish()

	// initially number of epochs param does not exist
	require.False(t, inMemParams.ParamsSubspace.Has(ctx, providertypes.KeyNumberOfEpochsToStartReceivingRewards))

	MigrateParams(ctx, *inMemParams.ParamsSubspace)

	// after migration, number of epochs epoch param should exist and be equal to default
	require.True(t, inMemParams.ParamsSubspace.Has(ctx, providertypes.KeyNumberOfEpochsToStartReceivingRewards))
	var numberOfEpochsParam int64
	inMemParams.ParamsSubspace.Get(ctx, providertypes.KeyNumberOfEpochsToStartReceivingRewards, &numberOfEpochsParam)
	require.Equal(t, providertypes.DefaultNumberOfEpochsToStartReceivingRewards, numberOfEpochsParam)
}
