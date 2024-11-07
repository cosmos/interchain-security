package v4

import (
	storetypes "cosmossdk.io/store/types"
)

const (
	LegacyPacketMaturityTimeKeyName = byte(12)
)

// CleanupState removes deprecated state
func CleanupState(store storetypes.KVStore) {
	removePrefix(store, LegacyPacketMaturityTimeKeyName)
}

func removePrefix(store storetypes.KVStore, prefix byte) {
	iterator := storetypes.KVStorePrefixIterator(store, []byte{prefix})
	defer iterator.Close()

	var keysToDel [][]byte
	for ; iterator.Valid(); iterator.Next() {
		keysToDel = append(keysToDel, iterator.Key())
	}
	for _, delKey := range keysToDel {
		store.Delete(delKey)
	}
}
