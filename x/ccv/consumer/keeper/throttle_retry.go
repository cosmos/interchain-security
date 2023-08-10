package keeper

import (
	"fmt"
	"time"

	sdktypes "github.com/cosmos/cosmos-sdk/types"

	consumertypes "github.com/cosmos/interchain-security/v3/x/ccv/consumer/types"
)

//
// Throttling with retries follows a finite-state machine design:
//
// 2 states: "No Slash" and "Standby".
// Initial State: "No Slash"
// Transition Event: ("No Slash", Slash packet sent) => ("Standby")
// Transition Event: ("Standby", V1Result ack received) => ("No Slash")
// Transition Event: ("Standby", Slash packet successfully handled) => ("No Slash")
// Internal Transition Event: ("Standby", Slash packet bounced) => ("Standby", with SlashRecord.WaitingOnReply = false)
// Transition Event: ("Standby", Retry sent) => ("Standby", new cycle)
//
// Description in words:
//
// 1. "No slash": If no slash record exists, the consumer is permitted to send packets from the pending packets queue.
// The consumer starts in this state from genesis.
//
// 2. On the event that a slash packet is obtained from the head of the pending packets queue and sent,
// a consumer transitions from "No Slash" to "Standby". A slash record is created upon entry to this state,
// and the consumer is now restricted from sending anymore packets.
//
// The slash packet remains at the head of the pending packets queue within the "Standby" state.
//
// - If the consumer receives a V1Result ack from the provider,
// OR if the consumer receives an ack from the provider that the slash packet was successfully handled,
// the consumer transitions from "Standby" to "No Slash".
// The slash record is cleared upon this transition, and the slash packet is popped from the pending packets queue.
//
// - Else if the consumer receives an ack from the provider that the slash packet was bounced (not handled),
// then SlashRecord.WaitingOnReply is set false, and the consumer retries sending the slash packet after a delay period.
//
// Once a retry is sent, the consumer enters a new cycle of the "Standby" state and the process repeats.
//
// This design is implemented below, and in relay.go under SendPackets() and OnAcknowledgementPacket().
//

// Retry delay period could be implemented as a param, but 1 hour is reasonable
const RetryDelayPeriod = time.Hour

// PacketSendingPermitted returns whether the consumer is allowed to send packets
// from the pending packets queue.
func (k Keeper) PacketSendingPermitted(ctx sdktypes.Context) bool {
	record, found := k.GetSlashRecord(ctx)
	if !found {
		// no slash record exists, send is permitted
		return true
	}
	if record.WaitingOnReply {
		// We are waiting on a reply from provider, block sending
		return false
	}
	// If retry delay period has elapsed, we can send again
	return ctx.BlockTime().After(record.SendTime.Add(RetryDelayPeriod))
}

func (k Keeper) UpdateSlashRecordOnSend(ctx sdktypes.Context) {
	record := consumertypes.NewSlashRecord(
		ctx.BlockTime(), // sendTime
		true,            // waitingOnReply
	)
	// We don't mind overwriting here, since this is either a retry or the first time we send a slash
	k.SetSlashRecord(ctx, record)
}

func (k Keeper) UpdateSlashRecordOnBounce(ctx sdktypes.Context) {
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
