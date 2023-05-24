package keeper

import (
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
