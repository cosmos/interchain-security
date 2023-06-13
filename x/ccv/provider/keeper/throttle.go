package keeper

import (
	"fmt"
	"time"

	sdktypes "github.com/cosmos/cosmos-sdk/types"
	providertypes "github.com/cosmos/interchain-security/v2/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v2/x/ccv/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

// This file contains functionality relevant to the throttling of slash and vsc matured packets, aka circuit breaker logic.

const vscMaturedHandledPerBlockLimit = 100

// HandleThrottleQueues iterates over the global slash entry queue, and
// handles all or some portion of throttled (slash and/or VSC matured) packet data received from
// consumer chains. The slash meter is decremented appropriately in this method.
func (k Keeper) HandleThrottleQueues(ctx sdktypes.Context, vscMaturedHandledThisBlock int) {
	meter := k.GetSlashMeter(ctx)
	// Return if meter is negative in value
	if meter.IsNegative() {
		return
	}

	// Return if vsc matured handle limit was already reached this block, during HandleLeadingVSCMaturedPackets.
	// It makes no practical difference for throttling logic to execute next block.
	// By doing this, we assure that all leading vsc matured packets were handled before any slash packets.
	if vscMaturedHandledThisBlock >= vscMaturedHandledPerBlockLimit {
		return
	}

	// Obtain all global slash entries, where only some of them may be handled in this method,
	// depending on the value of the slash meter.
	allEntries := k.GetAllGlobalSlashEntries(ctx)
	handledEntries := []providertypes.GlobalSlashEntry{}

	for _, globalEntry := range allEntries {
		// Subtract voting power that will be jailed/tombstoned from the slash meter
		providerAddr := providertypes.NewProviderConsAddress(globalEntry.ProviderValConsAddr)
		meter = meter.Sub(k.GetEffectiveValPower(ctx, providerAddr))

		// Handle one slash and any trailing vsc matured packet data instances by passing in
		// chainID and appropriate callbacks, relevant packet data is deleted in this method.

		k.HandlePacketDataForChain(ctx, globalEntry.ConsumerChainID, k.HandleSlashPacket, k.HandleVSCMaturedPacket, vscMaturedHandledThisBlock)
		handledEntries = append(handledEntries, globalEntry)

		// don't handle any more global entries if meter becomes negative in value
		if meter.IsNegative() {
			k.Logger(ctx).Info("negative slash meter value, no more slash packets will be handled", "meter", meter.Int64())
			break
		}
	}

	// Handled global entries are deleted after iteration is completed
	k.DeleteGlobalSlashEntries(ctx, handledEntries...)

	// Persist current value for slash meter
	k.SetSlashMeter(ctx, meter)

	if len(handledEntries) > 0 {
		k.Logger(ctx).Info("handled global slash entries", "count", len(handledEntries), "meter", meter.Int64())
	}
}

// Obtains the effective validator power relevant to a validator consensus address.
func (k Keeper) GetEffectiveValPower(ctx sdktypes.Context,
	valConsAddr providertypes.ProviderConsAddress,
) sdktypes.Int {
	// Obtain staking module val object from the provider's consensus address.
	// Note: if validator is not found or unbonded, this will be handled appropriately in HandleSlashPacket
	val, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, valConsAddr.ToSdkConsAddr())

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
// The handled data is then deleted from the queue.
//
// Note: Any packet data which is handled in this method is also deleted from the (consumer chain specific) queue.
func (k Keeper) HandlePacketDataForChain(ctx sdktypes.Context, consumerChainID string,
	slashPacketHandler func(sdktypes.Context, string, ccvtypes.SlashPacketData),
	vscMaturedPacketHandler func(sdktypes.Context, string, ccvtypes.VSCMaturedPacketData),
	vscMaturedHandledThisBlock int,
) {
	// Get slash packet data and trailing vsc matured packet data, handle it all.
	slashFound, slashData, vscMaturedData, seqNums := k.GetSlashAndTrailingData(ctx, consumerChainID)
	seqNumsHandled := []uint64{}
	if slashFound {
		slashPacketHandler(ctx, consumerChainID, slashData)
		// Slash packet should always be the first packet in the queue, so we can safely append the first seqNum.
		seqNumsHandled = append(seqNumsHandled, seqNums[0])
	}
	for idx, vscMData := range vscMaturedData {
		if vscMaturedHandledThisBlock >= vscMaturedHandledPerBlockLimit {
			// Break from for-loop, DeleteThrottledPacketData will still be called for this consumer
			break
		}
		vscMaturedPacketHandler(ctx, consumerChainID, vscMData)
		vscMaturedHandledThisBlock++
		// Append seq num for this vsc matured packet
		seqNumsHandled = append(seqNumsHandled, seqNums[idx+1]) // Note idx+1, since slash packet is at index 0
	}

	// Delete handled data after it has all been handled.
	k.DeleteThrottledPacketData(ctx, consumerChainID, seqNumsHandled...)
}

// InitializeSlashMeter initializes the slash meter to it's max value (also its allowance),
// and sets the replenish time candidate to one replenish period from current block time.
func (k Keeper) InitializeSlashMeter(ctx sdktypes.Context) {
	k.SetSlashMeter(ctx, k.GetSlashMeterAllowance(ctx))
	k.SetSlashMeterReplenishTimeCandidate(ctx)
}

// CheckForSlashMeterReplenishment checks if the slash meter should be replenished, and if so, replenishes it.
// Note: initial slash meter replenish time candidate is set in InitGenesis.
func (k Keeper) CheckForSlashMeterReplenishment(ctx sdktypes.Context) {
	// Replenish slash meter if current time is equal to or after the current replenish candidate time.
	if !ctx.BlockTime().UTC().Before(k.GetSlashMeterReplenishTimeCandidate(ctx)) {
		k.ReplenishSlashMeter(ctx)
		// Set replenish time candidate to one replenish period from now, since we just replenished.
		k.SetSlashMeterReplenishTimeCandidate(ctx)
	}

	// The following logic exists to ensure the slash meter is not greater than the allowance for this block,
	// in the event that the total voting power of the provider chain has decreased since previous blocks.

	// If slash meter is full, or more than full considering updated allowance/total power,
	allowance := k.GetSlashMeterAllowance(ctx)
	if k.GetSlashMeter(ctx).GTE(allowance) {

		// Update/set replenish time candidate to one replenish period from now.
		// This time candidate will be updated in every future block until the slash meter becomes NOT full.
		k.SetSlashMeterReplenishTimeCandidate(ctx)

		// Ensure the slash meter is not greater than allowance this block,
		// considering current total voting power.
		k.SetSlashMeter(ctx, allowance)
	}
}

func (k Keeper) ReplenishSlashMeter(ctx sdktypes.Context) {
	meter := k.GetSlashMeter(ctx)
	oldMeter := meter
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

	k.Logger(ctx).Debug("slash meter replenished",
		"old meter value", oldMeter.Int64(),
		"new meter value", meter.Int64(),
	)
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
	// MustNewDecFromStr should not panic, since the (string representation) of the slash meter replenish fraction
	// is validated in ValidateGenesis and anytime the param is mutated.
	decFrac := sdktypes.MustNewDecFromStr(strFrac)

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
func (k Keeper) QueueGlobalSlashEntry(ctx sdktypes.Context, entry providertypes.GlobalSlashEntry) {
	store := ctx.KVStore(k.storeKey)
	key := providertypes.GlobalSlashEntryKey(entry)
	bz := entry.ProviderValConsAddr
	store.Set(key, bz)
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

// GetAllGlobalSlashEntries returns all global slash entries from the queue.
//
// Note global slash entries are stored under keys with the following format:
// GlobalSlashEntryBytePrefix | uint64 recv time | ibc seq num | consumer chain id
// Thus, the returned array is ordered by recv time, then ibc seq num.
func (k Keeper) GetAllGlobalSlashEntries(ctx sdktypes.Context) []providertypes.GlobalSlashEntry {
	store := ctx.KVStore(k.storeKey)
	iterator := sdktypes.KVStorePrefixIterator(store, []byte{providertypes.GlobalSlashEntryBytePrefix})
	defer iterator.Close()

	entries := []providertypes.GlobalSlashEntry{}

	for ; iterator.Valid(); iterator.Next() {
		// MustParseGlobalSlashEntryKey should not panic, since we should be iterating over keys that're
		// assumed to be correctly serialized in QueueGlobalSlashEntry.
		recvTime, chainID, ibcSeqNum := providertypes.MustParseGlobalSlashEntryKey(iterator.Key())
		valAddr := providertypes.NewProviderConsAddress(iterator.Value())
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
	// if the queue does grow too large. MaxThrottledPackets should be set accordingly (quite large).
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
	k.Logger(ctx).Debug("incremented throttled packets size",
		"chainID", consumerChainID,
		"size", size+1,
	)
}

// QueueThrottledSlashPacketData queues the slash packet data for a chain-specific throttled packet data queue.
//
// Note: This queue is shared between pending slash packet data and pending vsc matured packet data.
func (k Keeper) QueueThrottledSlashPacketData(
	ctx sdktypes.Context, consumerChainID string, ibcSeqNum uint64, data ccvtypes.SlashPacketData,
) error {
	return k.QueueThrottledPacketData(ctx, consumerChainID, ibcSeqNum, data)
}

// QueueThrottledVSCMaturedPacketData queues the vsc matured packet data for a chain-specific throttled packet data queue.
//
// Note: This queue is shared between pending slash packet data and pending vsc matured packet data.
func (k Keeper) QueueThrottledVSCMaturedPacketData(
	ctx sdktypes.Context, consumerChainID string, ibcSeqNum uint64, data ccvtypes.VSCMaturedPacketData,
) error {
	return k.QueueThrottledPacketData(ctx, consumerChainID, ibcSeqNum, data)
}

// QueueThrottledPacketData queues a slash packet data or vsc matured packet data instance
// for the given consumer chain's queue.
//
// Note: This method returns an error because it is called from
// OnRecvSlashPacket and OnRecvVSCMaturedPacket, meaning we can return an ibc err ack to the
// counter party chain on error, instead of panicking this chain.
func (k Keeper) QueueThrottledPacketData(
	ctx sdktypes.Context, consumerChainID string, ibcSeqNum uint64, packetData interface{},
) error {
	store := ctx.KVStore(k.storeKey)

	var bz []byte
	var err error
	switch data := packetData.(type) {
	case ccvtypes.SlashPacketData:
		bz, err = data.Marshal()
		if err != nil {
			return fmt.Errorf("failed to marshal slash packet data: %v", err)
		}
		bz = append([]byte{slashPacketData}, bz...)
	case ccvtypes.VSCMaturedPacketData:
		bz, err = data.Marshal()
		if err != nil {
			return fmt.Errorf("failed to marshal vsc matured packet data: %v", err)
		}
		bz = append([]byte{vscMaturedPacketData}, bz...)
	default:
		// Indicates a developer error, this method should only be called
		// by tests, QueueThrottledSlashPacketData, or QueueThrottledVSCMaturedPacketData.
		panic(fmt.Sprintf("unexpected packet data type: %T", data))
	}

	store.Set(providertypes.ThrottledPacketDataKey(consumerChainID, ibcSeqNum), bz)
	k.IncrementThrottledPacketDataSize(ctx, consumerChainID)
	return nil
}

// GetLeadingVSCMaturedData returns the leading vsc matured packet data instances
// for a chain-specific throttled packet data queue. Ie the vsc matured packet data instances
// that do not have any slash packet data instances preceding them in the queue for consumerChainID.
func (k Keeper) GetLeadingVSCMaturedData(ctx sdktypes.Context, consumerChainID string) (
	vscMaturedData []ccvtypes.VSCMaturedPacketData, ibcSeqNums []uint64,
) {
	store := ctx.KVStore(k.storeKey)
	iteratorPrefix := providertypes.ChainIdWithLenKey(providertypes.ThrottledPacketDataBytePrefix, consumerChainID)
	iterator := sdktypes.KVStorePrefixIterator(store, iteratorPrefix)
	defer iterator.Close()

	// Iterate over the throttled packet data queue,
	// and return vsc matured packet data instances until we encounter a slash packet data instance.
	vscMaturedData = []ccvtypes.VSCMaturedPacketData{}
	ibcSeqNums = []uint64{}
	for ; iterator.Valid(); iterator.Next() {

		bz := iterator.Value()
		if bz[0] == slashPacketData {
			break
		} else if bz[0] != vscMaturedPacketData {
			// This case would indicate a developer error or store corruption,
			// since QueueThrottledPacketData should only queue slash packet data or vsc matured packet data.
			panic(fmt.Sprintf("unexpected packet data type: %d", bz[0]))
		}

		var data ccvtypes.VSCMaturedPacketData
		err := data.Unmarshal(bz[1:])
		if err != nil {
			// An error here would indicate something is very wrong,
			// vsc matured packet data is assumed to be correctly serialized in QueueThrottledPacketData.
			panic(fmt.Sprintf("failed to unmarshal vsc matured packet data: %v", err))
		}

		vscMaturedData = append(vscMaturedData, data)
		// The below func should not panic, since we should be iterating over keys that're
		// assumed to be correctly serialized in QueueThrottledPacketData.
		_, ibcSeqNum := providertypes.MustParseThrottledPacketDataKey(iterator.Key())
		ibcSeqNums = append(ibcSeqNums, ibcSeqNum)
	}
	return vscMaturedData, ibcSeqNums
}

// GetSlashAndTrailingData returns the first slash packet data instance and any
// trailing vsc matured packet data instances in the chain-specific throttled packet data queue.
//
// Note that throttled packet data is stored under keys with the following format:
// ThrottledPacketDataBytePrefix | len(chainID) | chainID | ibcSeqNum
// Thus, the returned array is in ascending order of ibc seq numbers.
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
					// An error here would indicate something is very wrong,
					// slash packet data is assumed to be correctly serialized in QueueThrottledPacketData.
					panic(fmt.Sprintf("failed to unmarshal slash packet data: %v", err))
				}
				slashFound = true
			}
		} else if bz[0] == vscMaturedPacketData {
			vscMData := ccvtypes.VSCMaturedPacketData{}
			if err := vscMData.Unmarshal(bz[1:]); err != nil {
				// An error here would indicate something is very wrong,
				// vsc matured packet data is assumed to be correctly serialized in QueueThrottledPacketData.
				panic(fmt.Sprintf("failed to unmarshal vsc matured packet data: %v", err))
			}
			vscMaturedData = append(vscMaturedData, vscMData)
		} else {
			// This case would indicate a developer error or store corruption,
			// since QueueThrottledPacketData should only queue slash packet data or vsc matured packet data.
			panic("invalid packet data type")
		}
		// The below func should not panic, since we should be iterating over keys that're
		// assumed to be correctly serialized in QueueThrottledPacketData.
		_, ibcSeqNum := providertypes.MustParseThrottledPacketDataKey(iterator.Key())
		ibcSeqNums = append(ibcSeqNums, ibcSeqNum)
	}
	return slashFound, slashData, vscMaturedData, ibcSeqNums
}

// GetAllThrottledPacketData returns all throttled packet data for a specific consumer chain.
//
// Note: This method is only used by tests and queries, hence why it returns redundant data as different types.
// Since this method executes on query, no panics are explicitly included.
func (k Keeper) GetAllThrottledPacketData(ctx sdktypes.Context, consumerChainID string) (
	slashData []ccvtypes.SlashPacketData, vscMaturedData []ccvtypes.VSCMaturedPacketData,
	rawOrderedData []interface{}, ibcSeqNums []uint64,
) {
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
				k.Logger(ctx).Error(fmt.Sprintf("failed to unmarshal slash packet data: %v", err))
				continue
			}
			slashData = append(slashData, d)
			rawOrderedData = append(rawOrderedData, d)
		case vscMaturedPacketData:
			d := ccvtypes.VSCMaturedPacketData{}
			if err := d.Unmarshal(bz[1:]); err != nil {
				k.Logger(ctx).Error(fmt.Sprintf("failed to unmarshal vsc matured packet data: %v", err))
				continue
			}
			vscMaturedData = append(vscMaturedData, d)
			rawOrderedData = append(rawOrderedData, d)
		default:
			k.Logger(ctx).Error(fmt.Sprintf("invalid packet data type: %v", bz[0]))
			continue
		}
		_, ibcSeqNum, err := providertypes.ParseThrottledPacketDataKey(iterator.Key())
		if err != nil {
			k.Logger(ctx).Error(fmt.Sprintf("failed to parse throttled packet data key: %v", err))
			continue
		}
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
		// Slash meter should be set as a part of InitGenesis and periodically updated by throttle logic,
		// there is no deletion method exposed, so nil bytes would indicate something is very wrong.
		panic("slash meter not set")
	}
	value := sdktypes.ZeroInt()
	err := value.Unmarshal(bz)
	if err != nil {
		// We should have obtained value bytes that were serialized in SetSlashMeter,
		// so an error here would indicate something is very wrong.
		panic(fmt.Sprintf("failed to unmarshal slash meter: %v", err))
	}
	return value
}

// SetSlashMeter sets the slash meter to the given signed int value
//
// Note: the value of this int should always be in the range of tendermint's [-MaxTotalVotingPower, MaxTotalVotingPower]
func (k Keeper) SetSlashMeter(ctx sdktypes.Context, value sdktypes.Int) {
	// TODO: remove these invariant panics once https://github.com/cosmos/interchain-security/issues/534 is solved.

	// The following panics are included since they are invariants for slash meter value.
	//
	// Explanation: slash meter replenish fraction is validated to be in range of [0, 1],
	// and MaxMeterValue = MaxAllowance = MaxReplenishFrac * MaxTotalVotingPower = 1 * MaxTotalVotingPower.
	if value.GT(sdktypes.NewInt(tmtypes.MaxTotalVotingPower)) {
		panic("slash meter value cannot be greater than tendermint's MaxTotalVotingPower")
	}
	// Further, HandleThrottleQueues should never subtract more than MaxTotalVotingPower from the meter,
	// since we cannot slash more than an entire validator set. So MinMeterValue = -1 * MaxTotalVotingPower.
	if value.LT(sdktypes.NewInt(-tmtypes.MaxTotalVotingPower)) {
		panic("slash meter value cannot be less than negative tendermint's MaxTotalVotingPower")
	}
	store := ctx.KVStore(k.storeKey)
	bz, err := value.Marshal()
	if err != nil {
		// A returned error for marshaling an int would indicate something is very wrong.
		panic(fmt.Sprintf("failed to marshal slash meter: %v", err))
	}
	store.Set(providertypes.SlashMeterKey(), bz)
}

// GetSlashMeterReplenishTimeCandidate returns the next UTC time the slash meter could potentially be replenished.
//
// Note: this value is the next time the slash meter will be replenished IFF the slash meter is NOT full.
// Otherwise this value will be updated in every future block until the slash meter becomes NOT full.
func (k Keeper) GetSlashMeterReplenishTimeCandidate(ctx sdktypes.Context) time.Time {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(providertypes.SlashMeterReplenishTimeCandidateKey())
	if bz == nil {
		// Slash meter replenish time candidate should be set as a part of InitGenesis and periodically updated by throttle logic,
		// there is no deletion method exposed, so nil bytes would indicate something is very wrong.
		panic("slash meter replenish time candidate not set")
	}
	time, err := sdktypes.ParseTimeBytes(bz)
	if err != nil {
		// We should have obtained value bytes that were serialized in SetSlashMeterReplenishTimeCandidate,
		// so an error here would indicate something is very wrong.
		panic(fmt.Sprintf("failed to parse slash meter replenish time candidate: %s", err))
	}
	return time.UTC()
}

// SetSlashMeterReplenishTimeCandidate sets the next time the slash meter may be replenished
// to the current block time + the configured slash meter replenish period.
//
// Note: this value is the next time the slash meter will be replenished IFF the slash meter is NOT full.
// Otherwise this value will be updated in every future block until the slash meter becomes NOT full.
func (k Keeper) SetSlashMeterReplenishTimeCandidate(ctx sdktypes.Context) {
	store := ctx.KVStore(k.storeKey)
	timeToStore := ctx.BlockTime().UTC().Add(k.GetSlashMeterReplenishPeriod(ctx))
	store.Set(providertypes.SlashMeterReplenishTimeCandidateKey(), sdktypes.FormatTimeBytes(timeToStore))
}
