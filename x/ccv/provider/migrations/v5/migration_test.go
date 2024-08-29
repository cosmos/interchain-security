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
	_, err := provKeeper.GetConsumerPowerShapingParameters(ctx, "chainID")
	require.Error(t, err)

	// migrate
	MigrateTopNForRegisteredChains(ctx, provKeeper)

	// after migration, top N should be 95
	powerShapingParameters, err := provKeeper.GetConsumerPowerShapingParameters(ctx, "chainID")
	require.NoError(t, err)
	require.Equal(t, uint32(95), powerShapingParameters.Top_N)
}
