package keeper

import (
	"fmt"
	"time"

	sdktypes "github.com/cosmos/cosmos-sdk/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

// This file contains functionality relevant to the throttling of slash and vsc matured packets, aka circuit breaker logic.

// High level TODOs
// TODO: still implement X amount of packets that halt the provider
// TODO: write up a readme explaining the design (no spec stuff, Marius can put this in ADR)
// TODO: in write up, explain that the feature could have been done with a single queue, but you'd need to
// periodically iterate over the queue to insert vsc matured packets, etc. With one global queue, and another queue
// for each chain, it's easy to reason about both:
// 1. How slash packets relate to other slash packets over time (regardless of chain) -> global queue
// 2. How slash packets relate to vsc matured packets from the same chain -> chain specific queue

// QueuePendingSlashPacket queues an entry in the parent queue, and queues the slash packet data to the chain specific queue.
func (k Keeper) QueuePendingSlashPacket(
	ctx sdktypes.Context, consumerChainID string, packet channeltypes.Packet, data ccvtypes.SlashPacketData) {

	// Queue a pending slash packet entry to the parent queue, which will be seen by the throttling logic
	k.QueuePendingSlashPacketEntry(ctx, providertypes.NewSlashPacketEntry(
		ctx.BlockTime(), // recv time
		consumerChainID, // consumer chain id that sent the packet
		data.Validator.Address))

	// Queue slash packet data in the same queue as vsc matured packet data, to enforce order of handling between the two types
	k.QueuePendingSlashPacketData(ctx,
		consumerChainID, // consumer chain id that sent the packet
		packet.Sequence, // IBC sequence number of the packet
		data)
}

// HandlePendingSlashPackets handles all or some portion of pending slash packets depending on circuit breaker logic.
// This method executes every end block routine
func (k Keeper) HandlePendingSlashPackets(ctx sdktypes.Context) {

	meter := k.GetSlashGasMeter(ctx)

	handledEntries := []providertypes.SlashPacketEntry{}
	k.IteratePendingSlashPacketEntries(ctx, func(entry providertypes.SlashPacketEntry) bool {

		valPower := k.stakingKeeper.GetLastValidatorPower(ctx, entry.ValAddr)
		meter.Sub(sdktypes.NewInt(valPower))

		k.HandlePendingSlashPacketByEntry(ctx, entry)

		handledEntries = append(handledEntries, entry)

		// Do not handle anymore slash packets if the meter has 0 or negative gas
		return !meter.IsPositive()
	})

	// Handled entries are deleted after iteration is completed
	k.DeletePendingSlashPacketEntries(ctx, handledEntries...)
	// Persist current value for slash gas meter
	k.SetSlashGasMeter(ctx, meter)
}

// HandlePendingSlashPacketByEntry retrieves the queued slash packet data relevant to the given entry,
// then handles the slash packet, and finally handles any trailing vsc matured packets in the
// chain specific pending packet data queue. Note that any handled (chain specific) pending packet data
// is deleted in this method. Whereas the entry itself is deleted after iteration is completed in HandlePendingSlashPackets.
func (k Keeper) HandlePendingSlashPacketByEntry(
	ctx sdktypes.Context, entry providertypes.SlashPacketEntry) {
	// TODO: handle slash packet, and all trailing vsc matured packets

	_, err := k.HandleSlashPacket(ctx, entry.ConsumerChainID,
		ccvtypes.SlashPacketData{}, // TODO
	)
	if err != nil {
		panic(fmt.Sprintf("failed to handle slash packet: %s", err.Error()))
	}
}

// TODO: Make an e2e test that asserts that the order of endblockers is correct between staking and ccv
// TODO: ie. the staking updates to voting power need to occur before circuit breaker logic, so circuit breaker has most up to date val powers.

// CheckForSlashMeterReplenishment checks if the slash gas meter should be replenished, and if so, replenishes it.
// TODO: hook this into endblocker, unit and e2e tests, tests must include odd time formats, since UTC is is used
func (k Keeper) CheckForSlashMeterReplenishment(ctx sdktypes.Context) {
	// TODO: Need to set initial replenishment time
	if ctx.BlockTime().UTC().After(k.GetLastSlashGasReplenishTime(ctx).Add(time.Hour)) {
		// TODO: Use param for replenish period, allowance, etc.
		// TODO: change code and documentation to reflect that this is a string fraction param
		slashGasAllowanceFraction := sdktypes.NewDec(5).Quo(sdktypes.NewDec(100)) // This will be a string param, ex: "0.05"

		// Compute slash gas allowance in units of tendermint voting power (integer), noting that total power changes over time
		totalPower := k.stakingKeeper.GetLastTotalPower(ctx)
		slashGasAllowance := sdktypes.NewInt(slashGasAllowanceFraction.MulInt(totalPower).RoundInt64())

		meter := k.GetSlashGasMeter(ctx)

		// Replenish gas up to gas allowance per period. That is, if meter was negative
		// before being replenished, it'll gain some additional gas. However, if the meter
		// was 0 or positive in value, it'll be replenished only up to it's allowance for the period.
		meter = meter.Add(slashGasAllowance)
		if meter.GT(slashGasAllowance) {
			meter = slashGasAllowance
		}
		k.SetSlashGasMeter(ctx, meter)
		k.SetLastSlashGasReplenishTime(ctx, ctx.BlockTime())
	}
}

//
// CRUD section
//

// TODO: Maybe this method just goes in the on recv method
func (k Keeper) HandleOrQueueVSCMaturedPacket(ctx sdktypes.Context, consumerChainID string, data ccvtypes.VSCMaturedPacketData) {
	// TODO: if queue for this chain is empty (no pending slash packets), handle vsc matured packet immediately
	// else queue it
	k.QueuePendingVSCMaturedPacketData(ctx, consumerChainID, 7, data) // TODO: hook seq number into this
}

// Highest level "parent" queue
// Note: this will overwrite the existing entry if a malicious consumer sends duplicate slash packets in the same block.
// TODO: unit test edge case where duplicate slash packet entries are added
func (k Keeper) QueuePendingSlashPacketEntry(ctx sdktypes.Context, entry providertypes.SlashPacketEntry) {
	store := ctx.KVStore(k.storeKey)
	key := providertypes.PendingSlashPacketEntryKey(entry)
	// Note: Val address is stored as value to assist in debugging. This could be removed for efficiency.
	store.Set(key, entry.ValAddr)
}

// GetAllPendingSlashPacketEntries returns all pending slash packet entries in the queue
// This method is used for testing purposes only
func (k Keeper) GetAllPendingSlashPacketEntries(ctx sdktypes.Context) (entries []providertypes.SlashPacketEntry) {
	k.IteratePendingSlashPacketEntries(ctx, func(entry providertypes.SlashPacketEntry) bool {
		entries = append(entries, entry)
		return false
	})
	return entries
}

// IteratePendingSlashPackets iterates over the pending slash packet entry queue and calls the provided callback
func (k Keeper) IteratePendingSlashPacketEntries(ctx sdktypes.Context, cb func(providertypes.SlashPacketEntry) bool) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdktypes.KVStorePrefixIterator(store, []byte{providertypes.PendingSlashPacketEntryBytePrefix})
	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		recvTime, chainID := providertypes.ParsePendingSlashPacketEntryKey(iterator.Key())
		valAddr := iterator.Value()
		entry := providertypes.NewSlashPacketEntry(recvTime, chainID, valAddr)
		if cb(entry) {
			break
		}
	}
}

// DeletePendingSlashPackets deletes the given entries from the pending slash packet entry queue
func (k Keeper) DeletePendingSlashPacketEntries(ctx sdktypes.Context, entries ...providertypes.SlashPacketEntry) {
	store := ctx.KVStore(k.storeKey)
	for _, entry := range entries {
		store.Delete(providertypes.PendingSlashPacketEntryKey(entry))
	}
}

// Pending packet data type enum, used to encode the type of packet data stored at each entry in the mutual queue.
const (
	slashPacketData byte = iota
	vscMaturedPacketData
)

// PanicIfTooMuchPendingPacketData is a sanity check to ensure that the pending packet data queue
// does not grow too large for a single consumer chain.
func (k Keeper) PanicIfTooMuchPendingPacketData(ctx sdktypes.Context, consumerChainID string) {
	// TODO, implement, and test?
	// if k.GetPendingPacketDataQueueSize(ctx) > 1000 {
	// 	panic(fmt.Sprintf("pending packet data queue size is too large: %d", k.GetPendingPacketDataQueueSize(ctx)))
	// }
}

// QueuePendingSlashPacketData queues the given slash packet data for the given consumer chain's queue
// Note: This queue is shared between pending slash packet data and pending vsc matured packet data
func (k Keeper) QueuePendingSlashPacketData(
	ctx sdktypes.Context, consumerChainID string, ibcSeqNum uint64, data ccvtypes.SlashPacketData) {

	k.PanicIfTooMuchPendingPacketData(ctx, consumerChainID)
	store := ctx.KVStore(k.storeKey)
	bz, err := data.Marshal()
	if err != nil {
		panic(fmt.Sprintf("failed to marshal slash packet data: %v", err))
	}
	bz = append([]byte{slashPacketData}, bz...)
	store.Set(providertypes.PendingPacketDataKey(consumerChainID, ibcSeqNum), bz)
}

// QueuePendingVSCMaturedPacketData queues the given vsc matured packet data for the given consumer chain's queue
// Note: This queue is shared between pending slash packet data and pending vsc matured packet data
func (k Keeper) QueuePendingVSCMaturedPacketData(
	ctx sdktypes.Context, consumerChainID string, ibcSeqNum uint64, data ccvtypes.VSCMaturedPacketData) {

	k.PanicIfTooMuchPendingPacketData(ctx, consumerChainID)
	store := ctx.KVStore(k.storeKey)
	bz, err := data.Marshal()
	if err != nil {
		panic(fmt.Sprintf("failed to marshal vsc matured packet data: %v", err))
	}
	bz = append([]byte{vscMaturedPacketData}, bz...)
	store.Set(providertypes.PendingPacketDataKey(consumerChainID, ibcSeqNum), bz)
}

// IteratePendingPacketData iterates over the pending packet data queue for a specific consumer chain
// (ordered by ibc seq number) and calls the provided callback
func (k Keeper) IteratePendingPacketData(ctx sdktypes.Context, consumerChainID string, cb func(uint64, interface{}) bool) {
	store := ctx.KVStore(k.storeKey)
	iteratorPrefix := append([]byte{providertypes.PendingPacketDataBytePrefix}, providertypes.HashString(consumerChainID)...)
	iterator := sdktypes.KVStorePrefixIterator(store, iteratorPrefix)
	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		var packetData interface{}
		var err error
		bz := iterator.Value()
		switch bz[0] {
		case slashPacketData:
			spd := ccvtypes.SlashPacketData{}
			err = spd.Unmarshal(bz[1:])
			packetData = spd
		case vscMaturedPacketData:
			vpd := ccvtypes.VSCMaturedPacketData{}
			err = vpd.Unmarshal(bz[1:])
			packetData = vpd
		default:
			panic("invalid packet data type")
		}
		if err != nil {
			panic(fmt.Sprintf("failed to unmarshal pending packet data: %v", err))
		}
		ibcSeqNum := providertypes.ParsePendingPacketDataKey(iterator.Key())
		if cb(ibcSeqNum, packetData) {
			break
		}
	}
}

// DeletePendingPacketData deletes the given entries (specified by their ibc seq number) from the pending packet data queue
func (k Keeper) DeletePendingPacketData(ctx sdktypes.Context, consumerChainID string, ibcSeqNumbers ...uint64) {
	store := ctx.KVStore(k.storeKey)
	for _, ibcSeqNum := range ibcSeqNumbers {
		store.Delete(providertypes.PendingPacketDataKey(consumerChainID, ibcSeqNum))
	}
}

// GetSlashGasMeter returns a meter (persisted as a signed int) which stores "slash gas",
// ie. an amount of voting power corresponding to an allowance of validators (with non-zero voting power)
// that can be jailed at a given time.
//
// Note: the value of this decimal should always be in the range of tendermint's [-MaxVotingPower, MaxVotingPower]
// TODO: If you keep slash gas meter as a percent, make sure it's clear that the param is a percent (put in name)
func (k Keeper) GetSlashGasMeter(ctx sdktypes.Context) sdktypes.Int {
	// TODO: is this the standard way to set a signed int?
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(providertypes.SlashGasMeterKey())
	if bz == nil {
		panic("slash gas meter not set")
	}
	value := sdktypes.ZeroInt()
	err := value.Unmarshal(bz)
	if err != nil {
		panic(fmt.Sprintf("failed to unmarshal slash gas meter: %v", err))
	}
	return value
}

// SetSlashGasMeter sets the "slash gas" meter to the given signed int value
//
// Note: the value of this decimal should always be in the range of tendermint's [-MaxVotingPower, MaxVotingPower]
func (k Keeper) SetSlashGasMeter(ctx sdktypes.Context, value sdktypes.Int) {
	if value.GT(sdktypes.NewInt(tmtypes.MaxTotalVotingPower)) {
		panic("slash gas meter value cannot be greater than tendermint's MaxTotalVotingPower")
	}
	if value.LT(sdktypes.NewInt(-tmtypes.MaxTotalVotingPower)) {
		panic("slash gas meter value cannot be less than negative tendermint's MaxTotalVotingPower")
	}
	store := ctx.KVStore(k.storeKey)
	bz, err := value.Marshal()
	if err != nil {
		panic(fmt.Sprintf("failed to marshal slash gas meter: %v", err))
	}
	store.Set(providertypes.SlashGasMeterKey(), bz)
}

// GetLastSlashGasReplenishTime returns the last UTC time the slash gas meter was replenished
func (k Keeper) GetLastSlashGasReplenishTime(ctx sdktypes.Context) time.Time {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(providertypes.LastSlashGasReplenishTimeKey())
	if bz == nil {
		panic("last slash gas replenish time not set")
	}
	time, err := sdktypes.ParseTimeBytes(bz)
	if err != nil {
		panic(fmt.Sprintf("failed to parse last slash gas replenish time: %s", err))
	}
	return time.UTC()
}

// SetLastSlashGasReplenishTime sets the last time the slash gas meter was replenished
func (k Keeper) SetLastSlashGasReplenishTime(ctx sdktypes.Context, time time.Time) {
	store := ctx.KVStore(k.storeKey)
	store.Set(providertypes.LastSlashGasReplenishTimeKey(), sdktypes.FormatTimeBytes(time.UTC()))
}
