package keeper

import (
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"
	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"

	consumertypes "github.com/cosmos/interchain-security/v3/x/ccv/consumer/types"
	ccvtypes "github.com/cosmos/interchain-security/v3/x/ccv/types"
)

// Migrator is a struct for handling in-place store migrations.
type Migrator struct {
	ccvConsumerKeeper     Keeper
	ccvConsumerParamSpace paramtypes.Subspace
}

// NewMigrator returns a new Migrator.
func NewMigrator(ccvConsumerKeeper Keeper, ccvConsumerParamSpace paramtypes.Subspace) Migrator {
	return Migrator{ccvConsumerKeeper: ccvConsumerKeeper, ccvConsumerParamSpace: ccvConsumerParamSpace}
}

// MigrateConsumerPacketData migrates consumer packet data according to
// https://github.com/cosmos/interchain-security/pull/1037
//
// Note an equivalent migration is not required for providers.
func (k Keeper) MigrateConsumerPacketData(ctx sdk.Context) error {
	// deserialize packet data from old format
	var depreciatedType ccvtypes.ConsumerPacketDataList
	store := ctx.KVStore(k.storeKey)
	bz := store.Get([]byte{consumertypes.PendingDataPacketsBytePrefix})
	if bz == nil {
		ctx.Logger().Info("no pending data packets to migrate")
		return nil
	}
	err := depreciatedType.Unmarshal(bz)
	if err != nil {
		return fmt.Errorf("failed to unmarshal pending data packets: %w", err)
	}

	// Delete old data
	store.Delete([]byte{consumertypes.PendingDataPacketsBytePrefix})

	// re-serialize packet data in new format, with the same key prefix,
	// where indexes are added internally to AppendPendingPacket.
	for _, data := range depreciatedType.List {
		k.AppendPendingPacket(ctx, data.Type, data.Data)
	}
	return nil
}

// TODO: the following hackyness could be removed if we're able to reference older versions of ICS.
// This would likely require go.mod split, and a testing module that could depend on multiple ICS versions.

func PendingDataPacketsKeyOnlyForTesting() []byte {
	return []byte{consumertypes.PendingDataPacketsBytePrefix} // Assumes keys haven't been shuffled
}

// Note: a better test of the old functionality would be to directly reference the old ICS version,
// including the version of ccv.ConsumerPacketDataList has a list of ccv.ConsumerPacketData without indexes.
func (k Keeper) SetPendingPacketsOnlyForTesting(ctx sdk.Context, packets ccvtypes.ConsumerPacketDataList) {
	store := ctx.KVStore(k.storeKey)
	bz, err := packets.Marshal()
	if err != nil {
		// This should never happen
		panic(fmt.Errorf("failed to marshal ConsumerPacketDataList: %w", err))
	}
	store.Set(PendingDataPacketsKeyOnlyForTesting(), bz)
}
