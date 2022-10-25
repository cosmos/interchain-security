package keeper

import (
	"fmt"

	"github.com/cosmos/cosmos-sdk/store/prefix"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/x/ccv/adminmodule/types"
)

func (k Keeper) GetAdmins(ctx sdk.Context) []string {
	admins := make([]string, 0)
	store := prefix.NewStore(ctx.KVStore(k.storeKey), []byte(types.AdminKey))

	iterator := sdk.KVStorePrefixIterator(store, []byte{})
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		admins = append(admins, string(iterator.Value()))
	}

	return admins
}

func (k Keeper) SetAdmin(ctx sdk.Context, admin string) {
	store := prefix.NewStore(ctx.KVStore(k.storeKey), []byte(types.AdminKey))
	store.Set([]byte(admin), []byte(admin))
}

func (k Keeper) RemoveAdmin(ctx sdk.Context, admin string) error {
	store := prefix.NewStore(ctx.KVStore(k.storeKey), []byte(types.AdminKey))
	storeAdmin := store.Get([]byte(admin))
	if storeAdmin == nil {
		return fmt.Errorf("couldn't find admin '%s'", admin)
	}

	store.Delete([]byte(admin))
	return nil
}

func (k Keeper) SetProviderICAAdmin(ctx sdk.Context, providerICAAdmin string) {
	store := ctx.KVStore(k.storeKey)
	store.Set([]byte(types.ProviderICAAdminKey), []byte(providerICAAdmin))
}

func (k Keeper) GetProviderICAAdmin(ctx sdk.Context) string {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get([]byte(types.ProviderICAAdminKey))
	if bz == nil {
		return ""
	}

	return string(bz)
}
