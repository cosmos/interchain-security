package keeper

import (
	"fmt"
	"time"

	sdktypes "github.com/cosmos/cosmos-sdk/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

// This file contains functionality relevant to the throttling of slash and vsc matured packets, aka circuit breaker logic.

// HandleThrottleQueues iterates over the global slash entry queue, and
// handles all or some portion of throttled (slash and/or VSC matured) packet data received from
// consumer chains. The slash meter is decremented appropriately in this method.
func (k Keeper) HandleThrottleQueues(ctx sdktypes.Context) {

	meter := k.GetSlashMeter(ctx)
	// Return if meter is negative in value
	if meter.IsNegative() {
		return
	}

	// Obtain all global slash entries, where only some of them may be handled in this method,
	// depending on the value of the slash meter.
	allEntries := k.GetAllGlobalSlashEntries(ctx)
	handledEntries := []providertypes.GlobalSlashEntry{}

	for _, globalEntry := range allEntries {
		// Subtract voting power that will be jailed/tombstoned from the slash meter
		meter = meter.Sub(k.GetEffectiveValPower(ctx, globalEntry.ProviderValConsAddr))

		// Handle one slash and any trailing vsc matured packet data instances by passing in
		// chainID and appropriate callbacks, relevant packet data is deleted in this method.

		k.HandlePacketDataForChain(ctx, globalEntry.ConsumerChainID, k.HandleSlashPacket, k.HandleVSCMaturedPacket)
		handledEntries = append(handledEntries, globalEntry)

		// don't handle any more global entries if meter becomes negative in value
		if meter.IsNegative() {
			break
		}
	}

	// Handled global entries are deleted after iteration is completed
	k.DeleteGlobalSlashEntries(ctx, handledEntries...)

	// Persist current value for slash meter
	k.SetSlashMeter(ctx, meter)
}

// Obtains the effective validator power relevant to a validator consensus address.
func (k Keeper) GetEffectiveValPower(ctx sdktypes.Context,
	valConsAddr sdktypes.ConsAddress, // Provider's validator consensus address
) sdktypes.Int {
	// Obtain staking module val object from the provider's consensus address.
	// Note: if validator is not found or unbonded, this will be handled appropriately in HandleSlashPacket
	val, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, valConsAddr)

	if !found || val.IsJailed() {
		// If validator is not found, or found but jailed, it's power is 0. This path is explicitly defined since the
		// staking keeper's LastValidatorPower values are not updated till the staking keeper's endblocker.
		return sdktypes.ZeroInt()
	} else {
		// Otherwise, return the staking keeper's LastValidatorPower value.
		return sdktypes.NewInt(k.stakingKeeper.GetLastValidatorPower(ctx, val.GetOperator()))
	}
}

// HandlePacketDataForChain handles only the first queued slash packet relevant to the passed consumer chainID,
// and then handles any trailing vsc matured packets in that (consumer chain specific) throttled packet data queue.
//
// Note: Any packet data which is handled in this method is also deleted from the (consumer chain specific) queue.
func (k Keeper) HandlePacketDataForChain(ctx sdktypes.Context, consumerChainID string,
	slashPacketHandler func(sdktypes.Context, string, ccvtypes.SlashPacketData),
	vscMaturedPacketHandler func(sdktypes.Context, string, ccvtypes.VSCMaturedPacketData),
) {
	// Get slash packet data and trailing vsc matured packet data, handle it all.
	slashFound, slashData, vscMaturedData, seqNums := k.GetSlashAndTrailingData(ctx, consumerChainID)
	if slashFound {
		slashPacketHandler(ctx, consumerChainID, slashData)
	}
	for _, vscMData := range vscMaturedData {
		vscMaturedPacketHandler(ctx, consumerChainID, vscMData)
	}

	// Delete handled data after it has all been handled.
	k.DeleteThrottledPacketData(ctx, consumerChainID, seqNums...)
}

// InitializeSlashMeter initializes the slash meter to it's max value (also its allowance),
// and sets the last replenish time to the current block time.
func (k Keeper) InitializeSlashMeter(ctx sdktypes.Context) {
	k.SetSlashMeter(ctx, k.GetSlashMeterAllowance(ctx))
	k.SetLastSlashMeterFullTime(ctx, ctx.BlockTime())
}

// CheckForSlashMeterReplenishment checks if the slash meter should be replenished, and if so, replenishes it.
// Note: initial "last slash meter full time" is set in InitGenesis.
func (k Keeper) CheckForSlashMeterReplenishment(ctx sdktypes.Context) {

	lastFullTime := k.GetLastSlashMeterFullTime(ctx)
	replenishPeriod := k.GetSlashMeterReplenishPeriod(ctx)

	// Replenish slash meter if enough time has passed since the last time it was full.
	if ctx.BlockTime().UTC().After(lastFullTime.Add(replenishPeriod)) {
		k.ReplenishSlashMeter(ctx)
	}

	// The following logic exists to ensure the slash meter is not greater than the allowance for this block,
	// in the event that the total voting power of the provider chain has decreased since previous blocks.

	// If slash meter is full, or more than full considering updated allowance/total power,
	allowance := k.GetSlashMeterAllowance(ctx)
	if k.GetSlashMeter(ctx).GTE(allowance) {

		// set the most recent time the slash meter was full to current block time.
		k.SetLastSlashMeterFullTime(ctx, ctx.BlockTime())

		// Ensure the slash meter is not greater than allowance this block,
		// considering current total voting power.
		k.SetSlashMeter(ctx, allowance)
	}
}

func (k Keeper) ReplenishSlashMeter(ctx sdktypes.Context) {

	meter := k.GetSlashMeter(ctx)
	allowance := k.GetSlashMeterAllowance(ctx)

	// Replenish meter up to allowance for this block. That is, if meter was negative
	// before being replenished, it'll become more positive in value. However, if the meter
	// was 0 or positive in value, it'll be replenished only up to it's allowance
	// for the current block.
	meter = meter.Add(allowance)
	if meter.GT(allowance) {
		meter = allowance
	}
	k.SetSlashMeter(ctx, meter)
}

// GetSlashMeterAllowance returns the amount of voting power units (int)
// that would be added to the slash meter for a replenishment that would happen this block,
// this allowance value also serves as the max value for the meter for this block.
//
// Note: allowance can change between blocks, since it is directly correlated to total voting power.
// The slash meter must be less than or equal to the allowance for this block, before any slash
// packet handling logic can be executed.
func (k Keeper) GetSlashMeterAllowance(ctx sdktypes.Context) sdktypes.Int {

	strFrac := k.GetSlashMeterReplenishFraction(ctx)
	decFrac, err := sdktypes.NewDecFromStr(strFrac)
	if err != nil {
		panic(fmt.Sprintf("failed to parse slash meter replenish fraction: %s", err))
	}

	// Compute allowance in units of tendermint voting power (integer),
	// noting that total power changes over time
	totalPower := k.stakingKeeper.GetLastTotalPower(ctx)

	roundedInt := sdktypes.NewInt(decFrac.MulInt(totalPower).RoundInt64())
	if roundedInt.IsZero() {
		k.Logger(ctx).Info("slash meter replenish fraction is too small " +
			"to add any allowance to the meter, considering bankers rounding")

		// Return non-zero allowance to guarantee some slash packets are eventually handled
		return sdktypes.NewInt(1)
	}
	return roundedInt
}

//
// CRUD section
//

// QueueGlobalSlashEntry queues an entry to the "global" slash packet queue, used for throttling val power changes
// related to jailing/tombstoning over time. This "global" queue is used to coordinate the order of slash packet handling
// between chains, whereas the chain-specific queue is used to coordinate the order of slash and vsc matured packets
// relevant to each chain.
func (k Keeper) QueueGlobalSlashEntry(ctx sdktypes.Context,
	entry providertypes.GlobalSlashEntry) {
	store := ctx.KVStore(k.storeKey)
	key := providertypes.GlobalSlashEntryKey(entry)
	store.Set(key, entry.ProviderValConsAddr)
}

// DeleteGlobalSlashEntriesForConsumer deletes all pending slash packet entries in the global queue,
// only relevant to a single consumer.
func (k Keeper) DeleteGlobalSlashEntriesForConsumer(ctx sdktypes.Context, consumerChainID string) {

	allEntries := k.GetAllGlobalSlashEntries(ctx)
	entriesToDel := []providertypes.GlobalSlashEntry{}

	for _, entry := range allEntries {
		if entry.ConsumerChainID == consumerChainID {
			entriesToDel = append(entriesToDel, entry)
		}
	}
	k.DeleteGlobalSlashEntries(ctx, entriesToDel...)
}

// GetAllGlobalSlashEntries returns all global slash entries from the queue
func (k Keeper) GetAllGlobalSlashEntries(ctx sdktypes.Context) []providertypes.GlobalSlashEntry {

	store := ctx.KVStore(k.storeKey)
	iterator := sdktypes.KVStorePrefixIterator(store, []byte{providertypes.GlobalSlashEntryBytePrefix})
	defer iterator.Close()

	entries := []providertypes.GlobalSlashEntry{}

	for ; iterator.Valid(); iterator.Next() {
		recvTime, chainID, ibcSeqNum := providertypes.ParseGlobalSlashEntryKey(iterator.Key())
		valAddr := iterator.Value()
		entry := providertypes.NewGlobalSlashEntry(recvTime, chainID, ibcSeqNum, valAddr)
		entries = append(entries, entry)
	}
	return entries
}

// DeleteGlobalSlashEntries deletes the given global entries from the global slash queue
func (k Keeper) DeleteGlobalSlashEntries(ctx sdktypes.Context, entries ...providertypes.GlobalSlashEntry) {
	store := ctx.KVStore(k.storeKey)
	for _, entry := range entries {
		store.Delete(providertypes.GlobalSlashEntryKey(entry))
	}
}

// Pending packet data type enum, used to encode the type of packet data stored at each entry in the mutual queue.
const (
	slashPacketData byte = iota
	vscMaturedPacketData
)

// GetThrottledPacketDataSize returns the size of the throttled packet data queue for the given consumer chain
func (k Keeper) GetThrottledPacketDataSize(ctx sdktypes.Context, consumerChainID string) uint64 {
	store := ctx.KVStore(k.storeKey)
	key := providertypes.ThrottledPacketDataSizeKey(consumerChainID)
	var size uint64
	bz := store.Get(key)
	if bz == nil {
		size = 0
	} else {
		size = sdktypes.BigEndianToUint64(bz)
	}
	return size
}

// SetThrottledPacketDataSize sets the size of the throttled packet data queue for the given consumer chain
func (k Keeper) SetThrottledPacketDataSize(ctx sdktypes.Context, consumerChainID string, size uint64) {

	// Sanity check to ensure that the chain-specific throttled packet data queue does not grow too
	// large for a single consumer chain. This check ensures that binaries would panic deterministically
	// if the queue does grow too large.
	if size >= uint64(k.GetMaxThrottledPackets(ctx)) {
		panic(fmt.Sprintf("throttled packet data queue for chain %s is too large: %d", consumerChainID, size))
	}

	store := ctx.KVStore(k.storeKey)
	key := providertypes.ThrottledPacketDataSizeKey(consumerChainID)
	bz := sdktypes.Uint64ToBigEndian(size)
	store.Set(key, bz)
}

// IncrementThrottledPacketDataSize increments the size of the throttled packet data
// queue for the given consumer chain.
func (k Keeper) IncrementThrottledPacketDataSize(ctx sdktypes.Context, consumerChainID string) {
	size := k.GetThrottledPacketDataSize(ctx, consumerChainID)
	k.SetThrottledPacketDataSize(ctx, consumerChainID, size+1)
}

// QueueThrottledSlashPacketData queues the slash packet data for a chain-specific throttled packet data queue.
//
// Note: This queue is shared between pending slash packet data and pending vsc matured packet data.
func (k Keeper) QueueThrottledSlashPacketData(
	ctx sdktypes.Context, consumerChainID string, ibcSeqNum uint64, data ccvtypes.SlashPacketData) {
	k.QueueThrottledPacketData(ctx, consumerChainID, ibcSeqNum, data)
}

// QueueThrottledVSCMaturedPacketData queues the vsc matured packet data for a chain-specific throttled packet data queue.
//
// Note: This queue is shared between pending slash packet data and pending vsc matured packet data.
func (k Keeper) QueueThrottledVSCMaturedPacketData(
	ctx sdktypes.Context, consumerChainID string, ibcSeqNum uint64, data ccvtypes.VSCMaturedPacketData) {
	k.QueueThrottledPacketData(ctx, consumerChainID, ibcSeqNum, data)
}

// QueueThrottledPacketData queues a slash packet data or vsc matured packet data instance
// for the given consumer chain's queue. This method is either used by tests, or called
// by higher level methods with type assertion.
func (k Keeper) QueueThrottledPacketData(
	ctx sdktypes.Context, consumerChainID string, ibcSeqNum uint64, packetData interface{}) {

	store := ctx.KVStore(k.storeKey)

	var bz []byte
	var err error
	switch data := packetData.(type) {
	case ccvtypes.SlashPacketData:
		bz, err = data.Marshal()
		if err != nil {
			panic(fmt.Sprintf("failed to marshal slash packet data: %v", err))
		}
		bz = append([]byte{slashPacketData}, bz...)
	case ccvtypes.VSCMaturedPacketData:
		bz, err = data.Marshal()
		if err != nil {
			panic(fmt.Sprintf("failed to marshal vsc matured packet data: %v", err))
		}
		bz = append([]byte{vscMaturedPacketData}, bz...)
	default:
		panic(fmt.Sprintf("unexpected packet data type: %T", data))
	}

	store.Set(providertypes.ThrottledPacketDataKey(consumerChainID, ibcSeqNum), bz)
	k.IncrementThrottledPacketDataSize(ctx, consumerChainID)
}

// GetSlashAndTrailingData returns the first slash packet data instance and any
// trailing vsc matured packet data instances in the chain-specific throttled packet data queue.
//
// Note: this method is not tested directly, but is covered indirectly
// by TestHandlePacketDataForChain and e2e tests.
func (k Keeper) GetSlashAndTrailingData(ctx sdktypes.Context, consumerChainID string) (
	slashFound bool, slashData ccvtypes.SlashPacketData, vscMaturedData []ccvtypes.VSCMaturedPacketData,
	// Note: this slice contains the IBC sequence numbers of the slash packet data
	// and trailing vsc matured packet data instances. This is used by caller to delete the
	// data after it has been handled.
	ibcSeqNums []uint64,
) {

	store := ctx.KVStore(k.storeKey)
	iteratorPrefix := providertypes.ChainIdWithLenKey(providertypes.ThrottledPacketDataBytePrefix, consumerChainID)
	iterator := sdktypes.KVStorePrefixIterator(store, iteratorPrefix)
	defer iterator.Close()

	slashFound = false
	slashData = ccvtypes.SlashPacketData{}
	vscMaturedData = []ccvtypes.VSCMaturedPacketData{}
	ibcSeqNums = []uint64{}

	for ; iterator.Valid(); iterator.Next() {

		bz := iterator.Value()
		if bz[0] == slashPacketData {
			if slashFound {
				// Break for-loop, we've already found first slash packet data instance.
				break
			} else {
				if err := slashData.Unmarshal(bz[1:]); err != nil {
					panic(fmt.Sprintf("failed to unmarshal pending packet data: %v", err))
				}
				slashFound = true
			}
		} else if bz[0] == vscMaturedPacketData {
			vscMData := ccvtypes.VSCMaturedPacketData{}
			if err := vscMData.Unmarshal(bz[1:]); err != nil {
				panic(fmt.Sprintf("failed to unmarshal pending packet data: %v", err))
			}
			vscMaturedData = append(vscMaturedData, vscMData)
		} else {
			panic("invalid packet data type")
		}

		_, ibcSeqNum := providertypes.MustParseThrottledPacketDataKey(iterator.Key())
		ibcSeqNums = append(ibcSeqNums, ibcSeqNum)
	}
	return slashFound, slashData, vscMaturedData, ibcSeqNums
}

// GetAllThrottledPacketData returns all throttled packet data for a specific consumer chain.
//
// Note: This method is only used by tests, hence why it returns redundant data as different types.
// This method is not unit tested, as it is a test util.
func (k Keeper) GetAllThrottledPacketData(ctx sdktypes.Context, consumerChainID string) (
	slashData []ccvtypes.SlashPacketData, vscMaturedData []ccvtypes.VSCMaturedPacketData,
	rawOrderedData []interface{}, ibcSeqNums []uint64) {

	slashData = []ccvtypes.SlashPacketData{}
	vscMaturedData = []ccvtypes.VSCMaturedPacketData{}
	rawOrderedData = []interface{}{}
	ibcSeqNums = []uint64{}

	store := ctx.KVStore(k.storeKey)
	iteratorPrefix := providertypes.ChainIdWithLenKey(providertypes.ThrottledPacketDataBytePrefix, consumerChainID)
	iterator := sdktypes.KVStorePrefixIterator(store, iteratorPrefix)
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		bz := iterator.Value()
		switch bz[0] {
		case slashPacketData:
			d := ccvtypes.SlashPacketData{}
			if err := d.Unmarshal(bz[1:]); err != nil {
				panic(fmt.Sprintf("failed to unmarshal slash packet data: %v", err))
			}
			slashData = append(slashData, d)
			rawOrderedData = append(rawOrderedData, d)
		case vscMaturedPacketData:
			d := ccvtypes.VSCMaturedPacketData{}
			if err := d.Unmarshal(bz[1:]); err != nil {
				panic(fmt.Sprintf("failed to unmarshal vsc matured packet data: %v", err))
			}
			vscMaturedData = append(vscMaturedData, d)
			rawOrderedData = append(rawOrderedData, d)
		default:
			panic(fmt.Sprintf("invalid packet data type: %v", bz[0]))
		}
		_, ibcSeqNum := providertypes.MustParseThrottledPacketDataKey(iterator.Key())
		ibcSeqNums = append(ibcSeqNums, ibcSeqNum)
	}

	return slashData, vscMaturedData, rawOrderedData, ibcSeqNums
}

// DeleteAllPacketDataForConsumer deletes all queued packet data for the given consumer chain.
func (k Keeper) DeleteThrottledPacketDataForConsumer(ctx sdktypes.Context, consumerChainID string) {

	store := ctx.KVStore(k.storeKey)
	iteratorPrefix := providertypes.ChainIdWithLenKey(providertypes.ThrottledPacketDataBytePrefix, consumerChainID)
	iterator := sdktypes.KVStorePrefixIterator(store, iteratorPrefix)
	defer iterator.Close()

	keysToDel := [][]byte{}
	for ; iterator.Valid(); iterator.Next() {
		keysToDel = append(keysToDel, iterator.Key())
	}
	// Delete data for this consumer
	for _, key := range keysToDel {
		store.Delete(key)
	}

	// Delete size of data queue for this consumer
	store.Delete(providertypes.ThrottledPacketDataSizeKey(consumerChainID))
}

// DeleteThrottledPacketData deletes the given throttled packet data instances
// (specified by their ibc seq number) from the chain-specific throttled packet data queue.
func (k Keeper) DeleteThrottledPacketData(ctx sdktypes.Context, consumerChainID string, ibcSeqNumbers ...uint64) {
	store := ctx.KVStore(k.storeKey)
	for _, ibcSeqNum := range ibcSeqNumbers {
		store.Delete(providertypes.ThrottledPacketDataKey(consumerChainID, ibcSeqNum))
	}
	// Decrement the size of the pending packet data queue
	sizeBeforeDeletion := k.GetThrottledPacketDataSize(ctx, consumerChainID)
	k.SetThrottledPacketDataSize(ctx, consumerChainID, sizeBeforeDeletion-uint64(len(ibcSeqNumbers)))
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

// GetLastSlashMeterFullTime returns the last UTC time the slash meter was full.
func (k Keeper) GetLastSlashMeterFullTime(ctx sdktypes.Context) time.Time {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(providertypes.LastSlashMeterFullTimeKey())
	if bz == nil {
		panic("last slash replenish time not set")
	}
	time, err := sdktypes.ParseTimeBytes(bz)
	if err != nil {
		panic(fmt.Sprintf("failed to parse last slash meter replenish time: %s", err))
	}
	return time.UTC()
}

// SetLastSlashMeterReplenishTime sets the most recent time the slash meter was full.
func (k Keeper) SetLastSlashMeterFullTime(ctx sdktypes.Context, time time.Time) {
	store := ctx.KVStore(k.storeKey)
	store.Set(providertypes.LastSlashMeterFullTimeKey(), sdktypes.FormatTimeBytes(time.UTC()))
}
