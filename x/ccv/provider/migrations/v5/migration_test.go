package v5

import (
	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	"testing"

	"github.com/stretchr/testify/require"

	testutil "github.com/cosmos/interchain-security/v5/testutil/keeper"
)

func TestMigrateParams(t *testing.T) {
	inMemParams := testutil.NewInMemKeeperParams(t)
	provKeeper, ctx, ctrl, _ := testutil.GetProviderKeeperAndCtx(t, inMemParams)
	defer ctrl.Finish()

	// set up a launched consumer chain
	provKeeper.SetConsumerClientId(ctx, "consumerId", "clientId")
	provKeeper.SetConsumerPhase(ctx, "consumerId", types.ConsumerPhase_CONSUMER_PHASE_LAUNCHED)

	// initially top N should not exist
	_, err := provKeeper.GetConsumerPowerShapingParameters(ctx, "consumerId")
	require.Error(t, err)

	// migrate
	MigrateTopNForRegisteredChains(ctx, provKeeper)

	// after migration, top N should be 95
	powerShapingParameters, err := provKeeper.GetConsumerPowerShapingParameters(ctx, "consumerId")
	require.NoError(t, err)
	require.Equal(t, uint32(95), powerShapingParameters.Top_N)
}
