package keeper_test

import (
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	testutil "github.com/cosmos/interchain-security/v3/testutil/keeper"
	consumertypes "github.com/cosmos/interchain-security/v3/x/ccv/consumer/types"
	ccvtypes "github.com/cosmos/interchain-security/v3/x/ccv/types"
)

func TestPacketSendingPermitted(t *testing.T) {
	consumerKeeper, ctx, ctrl, _ := testutil.GetConsumerKeeperAndCtx(t, testutil.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerKeeper.SetParams(ctx, ccvtypes.DefaultParams())

	ctx = ctx.WithBlockTime(time.Now())

	// No slash record exists, send is permitted
	slashRecord, found := consumerKeeper.GetSlashRecord(ctx)
	require.False(t, found)
	require.Zero(t, slashRecord)
	require.True(t, consumerKeeper.PacketSendingPermitted(ctx))

	// Update slash record on sending of slash packet
	consumerKeeper.UpdateSlashRecordOnSend(ctx)
	slashRecord, found = consumerKeeper.GetSlashRecord(ctx)
	require.True(t, found)
	require.True(t, slashRecord.WaitingOnReply)

	// Packet sending not permitted since we're waiting on a reply from provider
	require.False(t, consumerKeeper.PacketSendingPermitted(ctx))

	// Call update that happens when provider bounces slash packet
	consumerKeeper.UpdateSlashRecordOnBounce(ctx)
	slashRecord, found = consumerKeeper.GetSlashRecord(ctx)
	require.True(t, found)
	require.False(t, slashRecord.WaitingOnReply)

	// Packet sending still not permitted since retry delay period has not elapsed
	require.False(t, consumerKeeper.PacketSendingPermitted(ctx))

	// Elapse retry delay period
	period := consumerKeeper.GetRetryDelayPeriod(ctx)
	ctx = ctx.WithBlockTime(ctx.BlockTime().Add(2 * period))

	// Now packet sending is permitted again
	require.True(t, consumerKeeper.PacketSendingPermitted(ctx))
}

func TestThrottleRetryCRUD(t *testing.T) {
	consumerKeeper, ctx, ctrl, _ := testutil.GetConsumerKeeperAndCtx(t, testutil.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	slashRecord, found := consumerKeeper.GetSlashRecord(ctx)
	require.False(t, found)
	require.Zero(t, slashRecord)

	consumerKeeper.SetSlashRecord(ctx, consumertypes.SlashRecord{
		WaitingOnReply: true,
		SendTime:       ctx.BlockTime(),
	})

	slashRecord, found = consumerKeeper.GetSlashRecord(ctx)
	require.True(t, found)
	require.True(t, slashRecord.WaitingOnReply)
	require.Equal(t, ctx.BlockTime(), slashRecord.SendTime)

	// UpdateSlashRecordOnBounce should set WaitingOnReply to false, and leave SendTime unchanged
	oldBlocktime := ctx.BlockTime()
	ctx = ctx.WithBlockTime(ctx.BlockTime().Add(time.Hour))
	consumerKeeper.UpdateSlashRecordOnBounce(ctx)
	slashRecord, found = consumerKeeper.GetSlashRecord(ctx)
	require.True(t, found)
	require.False(t, slashRecord.WaitingOnReply)
	require.Equal(t, oldBlocktime, slashRecord.SendTime) // Old SendTime expected

	// UpdateSlashRecordOnSend should replace slash record with WaitingOnReply set to true, and new SendTime
	ctx = ctx.WithBlockTime(ctx.BlockTime().Add(time.Hour))
	consumerKeeper.UpdateSlashRecordOnSend(ctx)
	slashRecord, found = consumerKeeper.GetSlashRecord(ctx)
	require.True(t, found)
	require.True(t, slashRecord.WaitingOnReply)
	require.Equal(t, ctx.BlockTime(), slashRecord.SendTime)               // New SendTime expected
	require.Equal(t, oldBlocktime.Add(2*time.Hour), slashRecord.SendTime) // Sanity check

	consumerKeeper.ClearSlashRecord(ctx)
	slashRecord, found = consumerKeeper.GetSlashRecord(ctx)
	require.False(t, found)
	require.Zero(t, slashRecord)
}
