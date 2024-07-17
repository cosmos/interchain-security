package v8

import (
	"encoding/binary"
	"time"

	storetypes "cosmossdk.io/store/types"
	sdk "github.com/cosmos/cosmos-sdk/types"

	providerkeeper "github.com/cosmos/interchain-security/v5/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
)

// CompleteUnbondingOps completes all unbonding operations.
// Note that it must be executed before CleanupState.
func CompleteUnbondingOps(ctx sdk.Context, store storetypes.KVStore, pk providerkeeper.Keeper) {
	iterator := storetypes.KVStorePrefixIterator(store, []byte{providertypes.UnbondingOpBytePrefix})
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		id := binary.BigEndian.Uint64(iterator.Key()[1:])
		if err := pk.UnbondingCanComplete(ctx, id); err != nil {
			pk.Logger(ctx).Error("UnbondingCanComplete failed", "unbondingID", id, "error", err.Error())
		}
	}
}

// MigrateConsumerAddrsToPrune migrates the ConsumerAddrsToPrune index to ConsumerAddrsToPruneV2.
// Note: This migration must be done before removing the VscSendTimestamp index
func MigrateConsumerAddrsToPrune(ctx sdk.Context, store storetypes.KVStore, pk providerkeeper.Keeper) {
	iterator := storetypes.KVStorePrefixIterator(store, []byte{providertypes.ConsumerAddrsToPruneBytePrefix})
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		chainID, vscID, err := providertypes.ParseChainIdAndUintIdKey(providertypes.ConsumerAddrsToPruneBytePrefix, iterator.Key())
		if err != nil {
			pk.Logger(ctx).Error("ParseChainIdAndUintIdKey failed", "key", string(iterator.Key()))
			continue
		}
		// use the VscSendTimestamp index to compute the timestamp after which this consumer address can be pruned
		vscSendTimestampKey := providertypes.ChainIdAndUintIdKey(providertypes.VscSendTimestampBytePrefix, chainID, vscID)
		var sentTime time.Time
		if timeBz := store.Get(vscSendTimestampKey); timeBz != nil {
			if ts, err := sdk.ParseTimeBytes(timeBz); err == nil {
				sentTime = ts
			} else {
				pk.Logger(ctx).Error("MigrateConsumerAddrsToPrune failed parsing VSC send timestamp key", "error", err.Error())
				continue
			}
		} else {
			pk.Logger(ctx).Error(
				"MigrateConsumerAddrsToPrune cannot find VSC send timestamp",
				"chainID", chainID,
				"vscID", vscID,
			)
			continue
		}
		unbondingPeriod, err := pk.UnbondingTime(ctx)
		if err != nil {
			pk.Logger(ctx).Error(
				"MigrateConsumerAddrsToPrune cannot get unbonding period from staking module",
			)
			continue
		}
		pruneAfterTs := sentTime.Add(unbondingPeriod)

		var addrs providertypes.AddressList
		err = addrs.Unmarshal(iterator.Value())
		if err != nil {
			pk.Logger(ctx).Error("MigrateConsumerAddrsToPrune failed unmarshaling data from store", "key", string(iterator.Value()))
			continue
		}

		for _, addr := range addrs.Addresses {
			consumerAddr := providertypes.NewConsumerConsAddress(addr)
			pk.AppendConsumerAddrsToPrune(ctx, chainID, pruneAfterTs, consumerAddr)
		}
	}
}

// CleanupState removes deprecated state
func CleanupState(store storetypes.KVStore) {
	removePrefix(store, providertypes.MaturedUnbondingOpsByteKey)
	removePrefix(store, providertypes.UnbondingOpBytePrefix)
	removePrefix(store, providertypes.UnbondingOpIndexBytePrefix)
	removePrefix(store, providertypes.InitTimeoutTimestampBytePrefix)
	removePrefix(store, providertypes.VscSendTimestampBytePrefix)
	removePrefix(store, providertypes.VSCMaturedHandledThisBlockBytePrefix)
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
