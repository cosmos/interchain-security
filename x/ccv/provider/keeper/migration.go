package keeper

import (
	"fmt"
	sdk "github.com/cosmos/cosmos-sdk/types"

	sdktypes "github.com/cosmos/cosmos-sdk/types"
	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"

	providertypes "github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v3/x/ccv/types"
)

type Migrator struct {
	keeper         Keeper
	legacySubspace paramtypes.Subspace
}

// NewMigrator returns a new Migrator.
func NewMigrator(keeper Keeper, subspace paramtypes.Subspace) Migrator {
	return Migrator{
		keeper:         keeper,
		legacySubspace: subspace,
	}
}

// Migration from consensus version 2 to 3
func (m Migrator) Migrate2to3(ctx sdk.Context) error {
	return m.MigrateParams(ctx)
}

// MigrateParams migrates the provider module's parameters from the x/params to self store.
func (m Migrator) MigrateParams(ctx sdk.Context) error {
	params := GetParamsLegacy(ctx, m.legacySubspace)
	err := params.Validate()
	if err != nil {
		return err
	}
	m.keeper.SetParams(ctx, params)
	m.keeper.Logger(ctx).Info("successfully migrated provider parameters")
	return nil
}

// TODO: migrate v2 to v3 and make it work with migrating params (v3 to v4)
// // Migrator is a struct for handling in-place store migrations.
// type Migrator struct {
// 	providerKeeper Keeper
// 	paramSpace     paramtypes.Subspace
// }

// // NewMigrator returns a new Migrator.
// func NewMigrator(providerKeeper Keeper, paramSpace paramtypes.Subspace) Migrator {
// 	return Migrator{providerKeeper: providerKeeper, paramSpace: paramSpace}
// }

// // Migrate2to3 migrates x/ccvprovider state from consensus version 2 to 3.
// func (m Migrator) Migrate2to3(ctx sdktypes.Context) error {
// 	return m.providerKeeper.MigrateQueuedPackets(ctx)
// }

// func (k Keeper) MigrateQueuedPackets(ctx sdktypes.Context) error {
// 	for _, consumer := range k.GetAllConsumerChains(ctx) {
// 		slashData, vscmData := k.GetAllThrottledPacketData(ctx, consumer.ChainId)
// 		if len(slashData) > 0 {
// 			k.Logger(ctx).Error(fmt.Sprintf("slash data being dropped: %v", slashData))
// 		}
// 		for _, data := range vscmData {
// 			k.HandleVSCMaturedPacket(ctx, consumer.ChainId, data)
// 		}
// 		k.DeleteThrottledPacketDataForConsumer(ctx, consumer.ChainId)
// 	}
// 	return nil
// }

// // Pending packet data type enum, used to encode the type of packet data stored at each entry in the mutual queue.
// // Note this type is copy/pasted from throttle v1 code.
// const (
// 	slashPacketData byte = iota
// 	vscMaturedPacketData
// )

// // GetAllThrottledPacketData returns all throttled packet data for a given consumer chain, only used for 2 -> 3 migration.
// // Note this method is adapted from throttle v1 code.
// func (k Keeper) GetAllThrottledPacketData(ctx sdktypes.Context, consumerChainID string) (
// 	slashData []ccvtypes.SlashPacketData, vscMaturedData []ccvtypes.VSCMaturedPacketData,
// ) {
// 	slashData = []ccvtypes.SlashPacketData{}
// 	vscMaturedData = []ccvtypes.VSCMaturedPacketData{}

// 	store := ctx.KVStore(k.storeKey)
// 	iteratorPrefix := providertypes.ChainIdWithLenKey(providertypes.ThrottledPacketDataBytePrefix, consumerChainID)
// 	iterator := sdktypes.KVStorePrefixIterator(store, iteratorPrefix)
// 	defer iterator.Close()

// 	for ; iterator.Valid(); iterator.Next() {
// 		bz := iterator.Value()
// 		switch bz[0] {
// 		case slashPacketData:
// 			d := ccvtypes.SlashPacketData{}
// 			if err := d.Unmarshal(bz[1:]); err != nil {
// 				k.Logger(ctx).Error(fmt.Sprintf("failed to unmarshal slash packet data: %v", err))
// 				continue
// 			}
// 			slashData = append(slashData, d)
// 		case vscMaturedPacketData:
// 			d := ccvtypes.VSCMaturedPacketData{}
// 			if err := d.Unmarshal(bz[1:]); err != nil {
// 				k.Logger(ctx).Error(fmt.Sprintf("failed to unmarshal vsc matured packet data: %v", err))
// 				continue
// 			}
// 			vscMaturedData = append(vscMaturedData, d)
// 		default:
// 			k.Logger(ctx).Error(fmt.Sprintf("invalid packet data type: %v", bz[0]))
// 			continue
// 		}
// 	}

// 	return slashData, vscMaturedData
// }

// // Note this method is copy/pasted from throttle v1 code.
// func (k Keeper) DeleteThrottledPacketDataForConsumer(ctx sdktypes.Context, consumerChainID string) {
// 	store := ctx.KVStore(k.storeKey)
// 	iteratorPrefix := providertypes.ChainIdWithLenKey(providertypes.ThrottledPacketDataBytePrefix, consumerChainID)
// 	iterator := sdktypes.KVStorePrefixIterator(store, iteratorPrefix)
// 	defer iterator.Close()

// 	keysToDel := [][]byte{}
// 	for ; iterator.Valid(); iterator.Next() {
// 		keysToDel = append(keysToDel, iterator.Key())
// 	}
// 	// Delete data for this consumer
// 	for _, key := range keysToDel {
// 		store.Delete(key)
// 	}

// 	// Delete size of data queue for this consumer
// 	store.Delete(providertypes.ThrottledPacketDataSizeKey(consumerChainID))
// }

// // Note this method is adapted from throttle v1 code.
// func (k Keeper) QueueThrottledPacketDataOnlyForTesting(
// 	ctx sdktypes.Context, consumerChainID string, ibcSeqNum uint64, packetData interface{},
// ) error {
// 	store := ctx.KVStore(k.storeKey)

// 	var bz []byte
// 	var err error
// 	switch data := packetData.(type) {
// 	case ccvtypes.SlashPacketData:
// 		bz, err = data.Marshal()
// 		if err != nil {
// 			return fmt.Errorf("failed to marshal slash packet data: %v", err)
// 		}
// 		bz = append([]byte{slashPacketData}, bz...)
// 	case ccvtypes.VSCMaturedPacketData:
// 		bz, err = data.Marshal()
// 		if err != nil {
// 			return fmt.Errorf("failed to marshal vsc matured packet data: %v", err)
// 		}
// 		bz = append([]byte{vscMaturedPacketData}, bz...)
// 	default:
// 		// Indicates a developer error, this method should only be called
// 		// by tests, QueueThrottledSlashPacketData, or QueueThrottledVSCMaturedPacketData.
// 		panic(fmt.Sprintf("unexpected packet data type: %T", data))
// 	}

// 	store.Set(providertypes.ThrottledPacketDataKey(consumerChainID, ibcSeqNum), bz)
// 	return nil
// }
