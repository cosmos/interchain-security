package keeper

import (
	"fmt"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"
	consumertypes "github.com/cosmos/interchain-security/v2/x/ccv/consumer/types"
	ccvtypes "github.com/cosmos/interchain-security/v2/x/ccv/types"
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

// Note: If migrating from v1.2.0-multiden to v2.0.0, there are no migrations required.
// This is due to the fact that the former version includes both of:
// - https://github.com/cosmos/interchain-security/commit/54e9852d3c89a2513cd0170a56c6eec894fc878d
// - https://github.com/cosmos/interchain-security/pull/833
// both of which handle the introduction of new params.

// Migratev1Tov2 migrates a consumer from v1.0.0 to v2.0.0.
func (m Migrator) Migratev1Tov2(ctx sdk.Context) error {
	// Migrate params
	MigrateParamsv1Tov2(ctx, m.ccvConsumerParamSpace)

	return nil
}

// MigrateParamsv1Tov2 migrates the consumer CCV module params from v1.0.0 to v2.0.0,
// setting default values for new params.
func MigrateParamsv1Tov2(ctx sdk.Context, paramsSubspace paramtypes.Subspace) {
	// Get old params
	var enabled bool
	paramsSubspace.Get(ctx, consumertypes.KeyEnabled, &enabled)
	var blocksPerDistributionTransmission int64
	paramsSubspace.Get(ctx, consumertypes.KeyBlocksPerDistributionTransmission, &blocksPerDistributionTransmission)
	var distributionTransmissionChannel string
	paramsSubspace.Get(ctx, consumertypes.KeyDistributionTransmissionChannel, &distributionTransmissionChannel)
	var providerFeePoolAddrStr string
	paramsSubspace.Get(ctx, consumertypes.KeyProviderFeePoolAddrStr, &providerFeePoolAddrStr)
	var ccvTimeoutPeriod time.Duration
	paramsSubspace.Get(ctx, ccvtypes.KeyCCVTimeoutPeriod, &ccvTimeoutPeriod)
	var transferTimeoutPeriod time.Duration
	paramsSubspace.Get(ctx, consumertypes.KeyTransferTimeoutPeriod, &transferTimeoutPeriod)
	var consumerRedistributionFrac string
	paramsSubspace.Get(ctx, consumertypes.KeyConsumerRedistributionFrac, &consumerRedistributionFrac)
	var historicalEntries int64
	paramsSubspace.Get(ctx, consumertypes.KeyHistoricalEntries, &historicalEntries)
	var unbondingPeriod time.Duration
	paramsSubspace.Get(ctx, consumertypes.KeyConsumerUnbondingPeriod, &unbondingPeriod)

	// Recycle old params, set new params to default values
	defaultParams := consumertypes.DefaultParams()
	newParams := consumertypes.NewParams(
		enabled,
		blocksPerDistributionTransmission,
		distributionTransmissionChannel,
		providerFeePoolAddrStr,
		ccvTimeoutPeriod,
		transferTimeoutPeriod,
		consumerRedistributionFrac,
		historicalEntries,
		unbondingPeriod,
		defaultParams.SoftOptOutThreshold,
		defaultParams.RewardDenoms,
		defaultParams.ProviderRewardDenoms,
	)

	// Persist new params
	paramsSubspace.SetParamSet(ctx, &newParams)
}

// MigrateConsumerPacketData migrates consumer packet data according to
// https://github.com/cosmos/interchain-security/pull/1037
//
// Note an equivalent migration is not required for providers.
func (k Keeper) MigrateConsumerPacketData(ctx sdk.Context) {
	// deserialize packet data from old format
	var depreciatedType ccvtypes.ConsumerPacketDataList
	store := ctx.KVStore(k.storeKey)
	bz := store.Get([]byte{consumertypes.PendingDataPacketsBytePrefix})
	if bz == nil {
		ctx.Logger().Info("no pending data packets to migrate")
		return
	}
	err := depreciatedType.Unmarshal(bz)
	if err != nil {
		// An error here would indicate something is very wrong
		panic(fmt.Errorf("failed to unmarshal pending data packets: %w", err))
	}

	// Delete old data
	store.Delete([]byte{consumertypes.PendingDataPacketsBytePrefix})

	// re-serialize packet data in new format, with the same key prefix,
	// where indexes are added internally to AppendPendingPacket.
	for _, data := range depreciatedType.List {
		k.AppendPendingPacket(ctx, data.Type, data.Data)
	}
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
