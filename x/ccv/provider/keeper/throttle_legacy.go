package keeper

import (
	"fmt"

	sdktypes "github.com/cosmos/cosmos-sdk/types"

	providertypes "github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v5/x/ccv/types"
)

// Pending packet data type enum, used to encode the type of packet data stored at each entry in the mutual queue.
// Note this type is copy/pasted from throttle v1 code.
const (
	slashPacketData byte = iota
	vscMaturedPacketData
)

// Deprecated: LegacyGetAllThrottledPacketData is deprecated for ICS >= v4.0.0.
// LegacyGetAllThrottledPacketData returns all throttled packet data that was queued on the provider for a given consumer chain.
func (k Keeper) LegacyGetAllThrottledPacketData(ctx sdktypes.Context, consumerChainID string) (
	slashData []ccvtypes.SlashPacketData, vscMaturedData []ccvtypes.VSCMaturedPacketData,
) {
	slashData = []ccvtypes.SlashPacketData{}
	vscMaturedData = []ccvtypes.VSCMaturedPacketData{}

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
		case vscMaturedPacketData:
			d := ccvtypes.VSCMaturedPacketData{}
			if err := d.Unmarshal(bz[1:]); err != nil {
				k.Logger(ctx).Error(fmt.Sprintf("failed to unmarshal vsc matured packet data: %v", err))
				continue
			}
			vscMaturedData = append(vscMaturedData, d)
		default:
			k.Logger(ctx).Error(fmt.Sprintf("invalid packet data type: %v", bz[0]))
			continue
		}
	}

	return slashData, vscMaturedData
}

// Deprecated: LegacyDeleteThrottledPacketDataForConsumer is deprecated for ICS >= v4.0.0.
// LegacyDeleteThrottledPacketDataForConsumer removes all throttled packet data that was queued on the provider for a given consumer chain.
func (k Keeper) LegacyDeleteThrottledPacketDataForConsumer(ctx sdktypes.Context, consumerChainID string) {
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

// Deprecated: LegacyQueueThrottledPacketData is deprecated for ICS >= v4.0.0.
// LegacyQueueThrottledPacketData queues throttled packet data for a given consumer chain on the provider.
// The method should not be used because the provider does not process throttled packet data anymore.
func (k Keeper) LegacyQueueThrottledPacketData(
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
	return nil
}
