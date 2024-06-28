package vX

import (
	"encoding/binary"

	storetypes "github.com/cosmos/cosmos-sdk/store/types"
	sdk "github.com/cosmos/cosmos-sdk/types"

	providerkeeper "github.com/cosmos/interchain-security/v4/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/v4/x/ccv/types"
)

// CompleteUnbondingOps completes all unbonding operations.
// Note that it must be executed before CleanupState.
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

// CleanupState removes deprecated state
func CleanupState(store storetypes.KVStore) {
	removePrefix(store, providertypes.MaturedUnbondingOpsByteKey)
	removePrefix(store, providertypes.UnbondingOpBytePrefix)
	removePrefix(store, providertypes.UnbondingOpIndexBytePrefix)
	removePrefix(store, providertypes.VscSendTimestampBytePrefix)
	removePrefix(store, providertypes.VSCMaturedHandledThisBlockBytePrefix)
}

func removePrefix(store storetypes.KVStore, prefix byte) {
	iterator := sdk.KVStorePrefixIterator(store, []byte{prefix})
	defer iterator.Close()

	var keysToDel [][]byte
	for ; iterator.Valid(); iterator.Next() {
		keysToDel = append(keysToDel, iterator.Key())
	}
	for _, delKey := range keysToDel {
		store.Delete(delKey)
	}
}
