package keeper

import (
	sdktypes "github.com/cosmos/cosmos-sdk/types"
	consumertypes "github.com/cosmos/interchain-security/v3/x/ccv/consumer/types"
)

// TODO: Adjust SendPackets in relay.go

// TODO: incorporate retry delay

// TODO: will need good integration tests making sure this state is properly init, cleared, etc.

func (k Keeper) GetWaitingOnBouncingSlash(ctx sdktypes.Context) bool {
	store := ctx.KVStore(k.storeKey)
	return store.Has(consumertypes.WaitingOnBouncingSlashKey())
}

func (k Keeper) SetWaitingOnBouncingSlash(ctx sdktypes.Context) {
	store := ctx.KVStore(k.storeKey)
	store.Set(consumertypes.WaitingOnBouncingSlashKey(), []byte{1})
}

func (k Keeper) ClearWaitingOnBouncingSlash(ctx sdktypes.Context) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(consumertypes.WaitingOnBouncingSlashKey())
}
