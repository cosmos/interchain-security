package keeper

import (
	"fmt"
	"time"

	sdktypes "github.com/cosmos/cosmos-sdk/types"
	consumertypes "github.com/cosmos/interchain-security/v3/x/ccv/consumer/types"
)

// TODO: will need good integration tests making sure this state is properly init, cleared, etc.

// TODO: note on FSM design

func (k Keeper) PacketSendingPermitted(ctx sdktypes.Context) bool {
	record, found := k.GetSlashRecord(ctx)
	if !found {
		// no bouncing slash exists, send permitted
		return true
	}
	if record.WaitingOnReply {
		// We are waiting on a reply from provider, block sending
		return false
	}
	// retryDelayPeriod := k.GetParams(ctx).RetryDelayPeriod
	retryDelayPeriod := time.Hour
	timeSinceSend := ctx.BlockTime().Sub(record.SendTime)
	// If retry delay period has elapsed, we can send again
	retryPeriodElapsed := timeSinceSend >= retryDelayPeriod
	return retryPeriodElapsed
}

func (k Keeper) UpdateSlashRecordOnSend(ctx sdktypes.Context) {
	record := consumertypes.NewSlashRecord(
		ctx.BlockTime(), // sendTime
		true,            // waitingOnReply
	)
	// We don't mind overwriting here, since this is either a retry or the first time we send a slash
	k.SetSlashRecord(ctx, record)
}

func (k Keeper) UpdateSlashRecordOnReply(ctx sdktypes.Context) {
	record, found := k.GetSlashRecord(ctx)
	if !found {
		// This should never happen
		panic("could not find slash record, but reply was received from provider")
	}
	record.WaitingOnReply = false
	k.SetSlashRecord(ctx, record)
}

func (k Keeper) GetSlashRecord(ctx sdktypes.Context) (record consumertypes.SlashRecord, found bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(consumertypes.SlashRecordKey())
	if bz == nil {
		return record, false
	}
	err := record.Unmarshal(bz)
	if err != nil {
		// This should never happen
		panic(fmt.Sprintf("could not unmarshal slash record: %v", err))
	}
	return record, true
}

func (k Keeper) SetSlashRecord(ctx sdktypes.Context, record consumertypes.SlashRecord) {
	store := ctx.KVStore(k.storeKey)
	bz, err := record.Marshal()
	if err != nil {
		// This should never happen
		panic(fmt.Sprintf("could not marshal slash record: %v", err))
	}
	store.Set(consumertypes.SlashRecordKey(), bz)
}

func (k Keeper) ClearSlashRecord(ctx sdktypes.Context) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(consumertypes.SlashRecordKey())
}
