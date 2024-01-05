package v2

import (
	"fmt"

	storetypes "github.com/cosmos/cosmos-sdk/store/types"
	sdk "github.com/cosmos/cosmos-sdk/types"

	consumertypes "github.com/cosmos/interchain-security/v3/x/ccv/consumer/types"
	ccvtypes "github.com/cosmos/interchain-security/v3/x/ccv/types"
)

// MigrateConsumerPacketData migrates consumer packet data according to
// https://github.com/cosmos/interchain-security/pull/1037
//
// Note: an equivalent migration is not required for providers.
func MigrateConsumerPacketData(ctx sdk.Context, store storetypes.KVStore) error {
	// retrieve old data an deserialize
	var oldData consumertypes.ConsumerPacketDataList
	bz := store.Get([]byte{consumertypes.PendingDataPacketsBytePrefix})
	if bz == nil {
		ctx.Logger().Info("no pending data packets to migrate")
		return nil
	}
	err := oldData.Unmarshal(bz)
	if err != nil {
		return fmt.Errorf("failed to unmarshal pending data packets: %w", err)
	}

	// re-serialize packet data in new format, with the same key prefix,
	// index incrementation happens in getAndIncrementPendingPacketsIdx
	// the loop operations are equivalent to consumerkeeper.AppendPendingPacket()
	for _, data := range oldData.List {
		idx := getAndIncrementPendingPacketsIdx(ctx, store)
		key := consumertypes.PendingDataPacketsKey(idx)
		cpd := ccvtypes.NewConsumerPacketData(data.Type, data.Data)
		bz, err := cpd.Marshal()
		if err != nil {
			// This should never happen
			panic(fmt.Errorf("failed to marshal ConsumerPacketData: %w", err))
		}
		store.Set(key, bz)
	}

	store.Delete([]byte{consumertypes.PendingDataPacketsBytePrefix})
	return nil
}

// getAndIncrementPendingPacketsIdx returns the current pending packets index and increments it.
func getAndIncrementPendingPacketsIdx(ctx sdk.Context, store storetypes.KVStore) (toReturn uint64) {
	bz := store.Get(consumertypes.PendingPacketsIndexKey())
	if bz != nil {
		toReturn = sdk.BigEndianToUint64(bz)
	}
	toStore := toReturn + 1
	store.Set(consumertypes.PendingPacketsIndexKey(), sdk.Uint64ToBigEndian(toStore))
	return toReturn
}
