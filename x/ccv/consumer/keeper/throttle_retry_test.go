package keeper_test

import (
	"testing"

	testutil "github.com/cosmos/interchain-security/v3/testutil/keeper"
	consumertypes "github.com/cosmos/interchain-security/v3/x/ccv/consumer/types"
	ccvtypes "github.com/cosmos/interchain-security/v3/x/ccv/types"
	"github.com/stretchr/testify/require"
)

func TestBouncingSlashCRUD(t *testing.T) {
	consumerKeeper, ctx, ctrl, _ := testutil.GetConsumerKeeperAndCtx(t, testutil.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerPacketData := ccvtypes.ConsumerPacketData{
		Type: ccvtypes.SlashPacket,
		Data: &ccvtypes.ConsumerPacketData_SlashPacketData{},
	}

	ok, _ := consumerKeeper.GetBouncingSlash(ctx)
	require.False(t, ok)

	bouncingSlash, ok := consumertypes.NewBouncingSlash(consumerPacketData)
	require.True(t, ok)
	consumerKeeper.SetBouncingSlash(ctx, bouncingSlash)

	ok, bouncingSlash = consumerKeeper.GetBouncingSlash(ctx)
	require.True(t, ok)
	require.NotNil(t, bouncingSlash.SlashPacketData)
	require.False(t, bouncingSlash.RetryAllowed)

	bouncingSlash.RetryAllowed = true
	consumerKeeper.SetBouncingSlash(ctx, bouncingSlash)

	ok, bouncingSlash = consumerKeeper.GetBouncingSlash(ctx)
	require.True(t, ok)
	require.NotNil(t, bouncingSlash.SlashPacketData)
	require.True(t, bouncingSlash.RetryAllowed)

	consumerKeeper.DeleteBouncingSlash(ctx)
	ok, _ = consumerKeeper.GetBouncingSlash(ctx)
	require.False(t, ok)
}
