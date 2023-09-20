package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"

	consumertypes "github.com/cosmos/interchain-security/v3/x/ccv/consumer/types"
)

type Migrator struct {
	ccvProviderKeeper       Keeper
	ccvConsumerGenesisSpace paramtypes.Subspace
}

func NewMigrator(ccvProviderKeeper Keeper, ccvConsumerGenesisSpace paramtypes.Subspace) Migrator {
	return Migrator{ccvProviderKeeper: ccvProviderKeeper, ccvConsumerGenesisSpace: ccvConsumerGenesisSpace}
}

// Migrate GenesisState to ConsumerGenesisState
func (k Keeper) MigrateConsumerGenesisState(ctx sdk.Context) {
	//	var oldGenesisState consumertypes.
	store := ctx.KVStore(k.storeKey)
	bz := store.Get([]byte{consumertypes.PendingDataPacketsBytePrefix})
	if bz == nil {
		ctx.Logger().Info("no pending data packets to migrate")
		return
	}
	/* 	err := oldGenesisState.Unmarshal(bz)
	   	if err != nil {
	   		panic(fmt.Errorf("failed to unmarshal pending data packets: %w", err))
	   	}
	*/
}
