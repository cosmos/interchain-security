package keeper

import (
	"encoding/binary"
	"fmt"
	"time"

	sdktypes "github.com/cosmos/cosmos-sdk/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

// This file contains functionality relevant to the throttling of slash and vsc matured packets, aka circuit breaker logic.

// High level TODOs
// TODO: write up a readme explaining the design (no spec stuff, Marius can put this in ADR)
// TODO: in write up, explain that the feature could have been done with a single queue, but you'd need to
// periodically iterate over the queue to insert vsc matured packets, etc. With one global queue, and another queue
// for each chain, it's easy to reason about both:
// 1. How slash packets relate to other slash packets over time (regardless of chain) -> global queue
// 2. How slash packets relate to vsc matured packets from the same chain -> chain specific queue

// TODO: the onrecv handlers for both slash and vsc matured packets should be e2e tested with the method below.

// HandlePendingSlashPackets handles all or some portion of pending slash packets received by any consumer chain,
// depending on circuit breaker logic. This method executes every end block routine.
// TODO: This deserves an e2e test, not unit. You'll prob need to setup some staking module stuff tho.
// ^ do this in next commit, start with no packets to handle. No unit needed since HandlePacketDataForChain is unit tested.
func (k Keeper) HandlePendingSlashPackets(ctx sdktypes.Context) {

	meter := k.GetSlashMeter(ctx)
	handledEntries := []providertypes.SlashPacketEntry{}

	// Iterate through ordered (by received time) slash packet entries from any consumer chain
	k.IteratePendingSlashPacketEntries(ctx, func(entry providertypes.SlashPacketEntry) bool {

		// Obtain the validator power relevant to the slash packet that's about to be handled
		// (this power will be removed via jailing or tombstoning)
		valPower := k.stakingKeeper.GetLastValidatorPower(ctx, entry.ValAddr)

		// Subtract this power from the slash meter
		meter.Sub(sdktypes.NewInt(valPower))

		// Handle slash packet by passing in chainID and appropriate callbacks, relevant packet data is deleted in this method
		k.HandlePacketDataForChain(ctx, entry.ConsumerChainID, k.HandleSlashPacket, k.HandleVSCMaturedPacket)

		// Store handled entry to be deleted after iteration is completed
		handledEntries = append(handledEntries, entry)

		// Do not handle anymore slash packets if the meter has 0 or negative gas
		return !meter.IsPositive()
	})

	// Handled entries are deleted after iteration is completed
	k.DeletePendingSlashPacketEntries(ctx, handledEntries...)

	// Persist current value for slash gas meter
	k.SetSlashMeter(ctx, meter)
}

// HandlePacketDataForChain handles only the first queued slash packet relevant to the passed consumer chainID,
// and then handles any trailing vsc matured packets in that (consumer chain specific) queue.
//
// Note: Any packet data which is handled in this method is also deleted from the (consumer chain specific) queue.
func (k Keeper) HandlePacketDataForChain(ctx sdktypes.Context, consumerChainID string,
	slashPacketHandler func(sdktypes.Context, string, ccvtypes.SlashPacketData) (bool, error),
	vscMaturedPacketHandler func(sdktypes.Context, string, ccvtypes.VSCMaturedPacketData),
) {
	// Instantiate flag to indicate if one slash packet has been handled yet
	haveHandledSlash := false

	// Store ibc sequence numbers to delete data after iteration is completed
	seqNums := []uint64{}

	k.IteratePendingPacketData(ctx, consumerChainID, func(ibcSeqNum uint64, data interface{}) bool {

		switch data := data.(type) {

		case ccvtypes.SlashPacketData:
			if haveHandledSlash {
				// Break iteration, since we've already handled one slash packet
				return true
			}
			_, err := slashPacketHandler(ctx, consumerChainID, data)
			if err != nil {
				panic(fmt.Sprintf("failed to handle slash packet: %s", err))
			}
			haveHandledSlash = true

		case ccvtypes.VSCMaturedPacketData:
			// TODO: confirm this is safe, make tests around handling vsc matured packets immediately if no slash packets in queue
			if !haveHandledSlash {
				panic("data is corrupt, first data struct in queue should be slash packet data")
			}
			vscMaturedPacketHandler(ctx, consumerChainID, data)

		default:
			panic(fmt.Sprintf("unexpected pending packet data type: %T", data))
		}
		seqNums = append(seqNums, ibcSeqNum)
		return false
	})

	// Delete handled data after iteration is completed
	k.DeletePendingPacketData(ctx, consumerChainID, seqNums...)
}

// TODO: Make an e2e test that asserts that the order of endblockers is correct between staking and ccv
// TODO: ie. the staking updates to voting power need to occur before circuit breaker logic, so circuit breaker has most up to date val powers.
// From looking at app.go, this seems to be the case ^^

// CheckForSlashMeterReplenishment checks if the slash gas meter should be replenished, and if so, replenishes it.
// TODO: hook this into endblocker, unit and e2e tests, tests must include odd time formats, since UTC is is used
func (k Keeper) CheckForSlashMeterReplenishment(ctx sdktypes.Context) {
	// TODO: Need to set initial replenishment time
	if ctx.BlockTime().UTC().After(k.GetLastSlashMeterReplenishTime(ctx).Add(time.Hour)) {
		// TODO: Use param for replenish period, allowance, etc.
		// TODO: change code and documentation to reflect that this is a string fraction param
		slashGasAllowanceFraction := sdktypes.NewDec(5).Quo(sdktypes.NewDec(100)) // This will be a string param, ex: "0.05"

		// Compute slash gas allowance in units of tendermint voting power (integer), noting that total power changes over time
		totalPower := k.stakingKeeper.GetLastTotalPower(ctx)
		slashGasAllowance := sdktypes.NewInt(slashGasAllowanceFraction.MulInt(totalPower).RoundInt64())

		meter := k.GetSlashMeter(ctx)

		// Replenish gas up to gas allowance per period. That is, if meter was negative
		// before being replenished, it'll gain some additional gas. However, if the meter
		// was 0 or positive in value, it'll be replenished only up to it's allowance for the period.
		meter = meter.Add(slashGasAllowance)
		if meter.GT(slashGasAllowance) {
			meter = slashGasAllowance
		}
		k.SetSlashMeter(ctx, meter)
		k.SetLastSlashMeterReplenishTime(ctx, ctx.BlockTime())
	}
}

//
// CRUD section
//

// QueuePendingSlashPacketEntry queues an entry to the "parent" slash packet queue, used for throttling val power changes
// related to jailing/tombstoning over time. This "parent" queue is used to coordinate the order of slash packet handling
// between chains, whereas the chain specific queue is used to coordinate the order of slash and vsc matured packets
// relevant to each chain.
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
// TODO: Make this use a param, for now it's 15 (for tests you'll set param to 15 later on)
func (k Keeper) PanicIfTooMuchPendingPacketData(ctx sdktypes.Context, consumerChainID string) {
	size := k.GetPendingPacketDataSize(ctx, consumerChainID)
	if size > 15 {
		panic(fmt.Sprintf("pending packet data queue for chain %s is too large: %d", consumerChainID, size))
	}
}

// GetPendingPacketDataSize returns the size of the pending packet data queue for the given consumer chain
func (k Keeper) GetPendingPacketDataSize(ctx sdktypes.Context, consumerChainID string) uint64 {
	store := ctx.KVStore(k.storeKey)
	key := providertypes.PendingPacketDataSizeKey(consumerChainID)
	var size uint64
	bz := store.Get(key)
	if bz == nil {
		size = 0
	} else {
		size = binary.LittleEndian.Uint64(bz)
	}
	return size
}

// SetPendingPacketDataSize sets the size of the pending packet data queue for the given consumer chain
func (k Keeper) SetPendingPacketDataSize(ctx sdktypes.Context, consumerChainID string, size uint64) {
	store := ctx.KVStore(k.storeKey)
	key := providertypes.PendingPacketDataSizeKey(consumerChainID)
	bz := make([]byte, 8)
	binary.LittleEndian.PutUint64(bz, size)
	store.Set(key, bz)
}

// IncrementPendingPacketDataSize increments the size of the pending packet data queue for the given consumer chain
func (k Keeper) IncrementPendingPacketDataSize(ctx sdktypes.Context, consumerChainID string) {
	size := k.GetPendingPacketDataSize(ctx, consumerChainID)
	k.SetPendingPacketDataSize(ctx, consumerChainID, size+1)
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

	k.IncrementPendingPacketDataSize(ctx, consumerChainID)
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

	k.IncrementPendingPacketDataSize(ctx, consumerChainID)
}

// IteratePendingPacketData iterates over the pending packet data queue for a specific consumer chain
// (ordered by ibc seq number) and calls the provided callback
func (k Keeper) IteratePendingPacketData(ctx sdktypes.Context, consumerChainID string, cb func(uint64, interface{}) bool) {
	store := ctx.KVStore(k.storeKey)
	iteratorPrefix := providertypes.ChainIdWithLenKey(providertypes.PendingPacketDataBytePrefix, consumerChainID)
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
		_, ibcSeqNum, err := providertypes.ParsePendingPacketDataKey(iterator.Key())
		if err != nil {
			panic(fmt.Sprintf("failed to parse pending packet data key: %v", err))
		}
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
	// Decrement the size of the pending packet data queue
	sizeBeforeDeletion := k.GetPendingPacketDataSize(ctx, consumerChainID)
	k.SetPendingPacketDataSize(ctx, consumerChainID, sizeBeforeDeletion-uint64(len(ibcSeqNumbers)))
}

// GetSlashMeter returns a meter (persisted as a signed int) which stores an amount of voting power, corresponding
// to an allowance of validators that can be jailed/tombstoned over time.
//
// Note: the value of this int should always be in the range of tendermint's [-MaxVotingPower, MaxVotingPower]
func (k Keeper) GetSlashMeter(ctx sdktypes.Context) sdktypes.Int {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(providertypes.SlashMeterKey())
	if bz == nil {
		panic("slash meter not set")
	}
	value := sdktypes.ZeroInt()
	err := value.Unmarshal(bz)
	if err != nil {
		panic(fmt.Sprintf("failed to unmarshal slash meter: %v", err))
	}
	return value
}

// SetSlashMeter sets the slash meter to the given signed int value
//
// Note: the value of this int should always be in the range of tendermint's [-MaxVotingPower, MaxVotingPower]
func (k Keeper) SetSlashMeter(ctx sdktypes.Context, value sdktypes.Int) {
	if value.GT(sdktypes.NewInt(tmtypes.MaxTotalVotingPower)) {
		panic("slash meter value cannot be greater than tendermint's MaxTotalVotingPower")
	}
	if value.LT(sdktypes.NewInt(-tmtypes.MaxTotalVotingPower)) {
		panic("slash meter value cannot be less than negative tendermint's MaxTotalVotingPower")
	}
	store := ctx.KVStore(k.storeKey)
	bz, err := value.Marshal()
	if err != nil {
		panic(fmt.Sprintf("failed to marshal slash meter: %v", err))
	}
	store.Set(providertypes.SlashMeterKey(), bz)
}

// GetLastSlashMeterReplenishTime returns the last UTC time the slash meter was replenished
func (k Keeper) GetLastSlashMeterReplenishTime(ctx sdktypes.Context) time.Time {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(providertypes.LastSlashMeterReplenishTimeKey())
	if bz == nil {
		panic("last slash replenish time not set")
	}
	time, err := sdktypes.ParseTimeBytes(bz)
	if err != nil {
		panic(fmt.Sprintf("failed to parse last slash meter replenish time: %s", err))
	}
	return time.UTC()
}

// SetLastSlashMeterReplenishTime sets the last time the slash meter was replenished
func (k Keeper) SetLastSlashMeterReplenishTime(ctx sdktypes.Context, time time.Time) {
	store := ctx.KVStore(k.storeKey)
	store.Set(providertypes.LastSlashMeterReplenishTimeKey(), sdktypes.FormatTimeBytes(time.UTC()))
}
