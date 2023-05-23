package keeper

import (
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"
	v2consumertypes "github.com/cosmos/interchain-security/v2/x/ccv/consumer/types"
	v1consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	v1ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"
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

func (m Migrator) Migratev1p0To1p3(ctx sdk.Context) error {
	// Migrate params
	MigrateParamsv1p0To1p3(ctx, m.ccvConsumerParamSpace)

	return nil
}

// MigrateParamsv1p0To1p3 migrates the consumer CCV module params from v1.0.0 to v1.3.0,
// setting default values for new params.
func MigrateParamsv1p0To1p3(ctx sdk.Context, paramsSubspace paramtypes.Subspace) {
	// Get old params
	var enabled bool
	paramsSubspace.Get(ctx, v1consumertypes.KeyEnabled, &enabled)
	var blocksPerDistributionTransmission int64
	paramsSubspace.Get(ctx, v1consumertypes.KeyBlocksPerDistributionTransmission, &blocksPerDistributionTransmission)
	var distributionTransmissionChannel string
	paramsSubspace.Get(ctx, v1consumertypes.KeyDistributionTransmissionChannel, &distributionTransmissionChannel)
	var providerFeePoolAddrStr string
	paramsSubspace.Get(ctx, v1consumertypes.KeyProviderFeePoolAddrStr, &providerFeePoolAddrStr)
	var ccvTimeoutPeriod time.Duration
	paramsSubspace.Get(ctx, v1ccvtypes.KeyCCVTimeoutPeriod, &ccvTimeoutPeriod)
	var transferTimeoutPeriod time.Duration
	paramsSubspace.Get(ctx, v1consumertypes.KeyTransferTimeoutPeriod, &transferTimeoutPeriod)
	var consumerRedistributionFrac string
	paramsSubspace.Get(ctx, v1consumertypes.KeyConsumerRedistributionFrac, &consumerRedistributionFrac)
	var historicalEntries int64
	paramsSubspace.Get(ctx, v1consumertypes.KeyHistoricalEntries, &historicalEntries)
	var unbondingPeriod time.Duration
	paramsSubspace.Get(ctx, v1consumertypes.KeyConsumerUnbondingPeriod, &unbondingPeriod)

	// Recycle old params, set new params to default values
	defaultParams := v2consumertypes.DefaultParams()
	newParams := v2consumertypes.NewParams(
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
