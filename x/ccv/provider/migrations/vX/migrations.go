package vX

import (
	"encoding/binary"
	"time"

	storetypes "github.com/cosmos/cosmos-sdk/store/types"
	sdk "github.com/cosmos/cosmos-sdk/types"

	providerkeeper "github.com/cosmos/interchain-security/v4/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/v4/x/ccv/types"
)

// CompleteUnbondingOps completes all unbonding operations
func CompleteUnbondingOps(ctx sdk.Context, store storetypes.KVStore, pk providerkeeper.Keeper, sk ccv.StakingKeeper) {
	iterator := sdk.KVStorePrefixIterator(store, []byte{providertypes.UnbondingOpBytePrefix})
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		id := binary.BigEndian.Uint64(iterator.Key()[1:])
		if err := sk.UnbondingCanComplete(ctx, id); err != nil {
			pk.Logger(ctx).Error("UnbondingCanComplete failed", "unbondingID", id, "error", err.Error())
		}
	}
}

// MigrateConsumerAddrsToPrune migrates the ConsumerAddrsToPrune index to ConsumerAddrsToPruneV2.
// Note: This migration must be done before removing the VscSendTimestamp index
func MigrateConsumerAddrsToPrune(ctx sdk.Context, store storetypes.KVStore, pk providerkeeper.Keeper, sk ccv.StakingKeeper) {
	iterator := sdk.KVStorePrefixIterator(store, []byte{providertypes.ConsumerAddrsToPruneBytePrefix})
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		chainID, vscID, err := providertypes.ParseChainIdAndUintIdKey(providertypes.ConsumerAddrsToPruneBytePrefix, iterator.Key())
		if err != nil {
			pk.Logger(ctx).Error("ParseChainIdAndUintIdKey failed", "key", string(iterator.Key()))
		}
		// use the VscSendTimestamp index to compute the timestamp after which this consumer address can be pruned
		vscSendTimestampKey := providertypes.ChainIdAndUintIdKey(providertypes.VscSendTimestampBytePrefix, chainID, vscID)
		sentTime := time.Time{}
		if timeBz := store.Get(vscSendTimestampKey); timeBz != nil {
			if ts, err := sdk.ParseTimeBytes(timeBz); err == nil {
				sentTime = ts
			}
		}
		pruneAfterTs := sentTime.Add(sk.UnbondingTime(ctx))

		var addrs providertypes.AddressList
		err = addrs.Unmarshal(iterator.Value())
		if err != nil {
			pk.Logger(ctx).Error("MigrateConsumerAddrsToPrune failed unmarshaling data from store", "key", string(iterator.Value()))
		}

		for _, addr := range addrs.Addresses {
			consumerAddr := providertypes.NewConsumerConsAddress(addr)
			pk.AppendConsumerAddrsToPruneV2(ctx, chainID, pruneAfterTs, consumerAddr)
		}
	}
}

// CleanupState removes deprecated state
func CleanupState(ctx sdk.Context, store storetypes.KVStore) error {
	removePrefix(store, providertypes.MaturedUnbondingOpsByteKey)
	removePrefix(store, providertypes.UnbondingOpBytePrefix)
	removePrefix(store, providertypes.UnbondingOpIndexBytePrefix)
	removePrefix(store, providertypes.VscSendTimestampBytePrefix)
	removePrefix(store, providertypes.VSCMaturedHandledThisBlockBytePrefix)

	return nil
}

func removePrefix(store storetypes.KVStore, prefix byte) error {
	iterator := sdk.KVStorePrefixIterator(store, []byte{prefix})
	defer iterator.Close()

	var keysToDel [][]byte
	for ; iterator.Valid(); iterator.Next() {
		keysToDel = append(keysToDel, iterator.Key())
	}
	for _, delKey := range keysToDel {
		store.Delete(delKey)
	}

	return nil
}
