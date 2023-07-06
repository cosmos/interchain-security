package keeper_test

import (
	"testing"
	"time"

	testutil "github.com/cosmos/interchain-security/v3/testutil/keeper"
	consumertypes "github.com/cosmos/interchain-security/v3/x/ccv/consumer/types"
	"github.com/stretchr/testify/require"
)

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
