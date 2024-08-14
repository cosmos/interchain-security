package v8

import (
	"encoding/binary"
	"time"

	storetypes "cosmossdk.io/store/types"
	sdk "github.com/cosmos/cosmos-sdk/types"

	providerkeeper "github.com/cosmos/interchain-security/v5/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
)

const (
	LegacyUnbondingOpBytePrefix                = byte(11)
	LegacyConsumerAddrsToPruneBytePrefix       = byte(25)
	LegacyMaturedUnbondingOpsByteKey           = byte(1)
	LegacyUnbondingOpIndexBytePrefix           = byte(12)
	LegacyInitTimeoutTimestampBytePrefix       = byte(8)
	LegacyVscSendTimestampBytePrefix           = byte(18)
	LegacyVSCMaturedHandledThisBlockBytePrefix = byte(28)
)

// CompleteUnbondingOps completes all unbonding operations.
// Note that it must be executed before CleanupState.
func CompleteUnbondingOps(ctx sdk.Context, store storetypes.KVStore, pk providerkeeper.Keeper) {
	iterator := storetypes.KVStorePrefixIterator(store, []byte{LegacyUnbondingOpBytePrefix})
	defer func() {
		if err := iterator.Close(); err != nil {
			pk.Logger(ctx).Error("Failed to close iterator", "error", err)
		}
	}()

	for ; iterator.Valid(); iterator.Next() {
		id := binary.BigEndian.Uint64(iterator.Key()[1:])
		if err := pk.UnbondingCanComplete(ctx, id); err != nil {
			pk.Logger(ctx).Error("UnbondingCanComplete failed", "unbondingID", id, "error", err.Error())
		}
	}
}

// MigrateConsumerAddrsToPrune migrates the ConsumerAddrsToPrune index to ConsumerAddrsToPruneV2.
// Note: This migration must be done before removing the VscSendTimestamp index
func MigrateConsumerAddrsToPrune(ctx sdk.Context, store storetypes.KVStore, pk providerkeeper.Keeper) error {
	iterator := storetypes.KVStorePrefixIterator(store, []byte{LegacyConsumerAddrsToPruneBytePrefix})
	defer iterator.Close()

	unbondingPeriod, err := pk.UnbondingTime(ctx)
	if err != nil {
		return err
	}

	for ; iterator.Valid(); iterator.Next() {
		chainID, vscID, err := providertypes.ParseChainIdAndUintIdKey(LegacyConsumerAddrsToPruneBytePrefix, iterator.Key())
		if err != nil {
			pk.Logger(ctx).Error("ParseChainIdAndUintIdKey failed while migrating ConsumerAddrsToPrune",
				"key", string(iterator.Key()),
				"error", err.Error(),
			)
			continue
		}
		// use the VscSendTimestamp index to compute the timestamp after which this consumer address can be pruned
		vscSendTimestampKey := providertypes.ChainIdAndUintIdKey(LegacyVscSendTimestampBytePrefix, chainID, vscID)
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
		pruneAfterTs := sentTime.Add(unbondingPeriod).UTC()

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

	return nil
}

// CleanupState removes deprecated state
func CleanupState(store storetypes.KVStore) {
	removePrefix(store, LegacyMaturedUnbondingOpsByteKey)
	removePrefix(store, LegacyUnbondingOpBytePrefix)
	removePrefix(store, LegacyUnbondingOpIndexBytePrefix)
	removePrefix(store, LegacyInitTimeoutTimestampBytePrefix)
	removePrefix(store, LegacyVscSendTimestampBytePrefix)
	removePrefix(store, LegacyVSCMaturedHandledThisBlockBytePrefix)
	removePrefix(store, LegacyConsumerAddrsToPruneBytePrefix)
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
