package v7

import (
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	ibctmtypes "github.com/cosmos/ibc-go/v8/modules/light-clients/07-tendermint"
	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"

	ccvtypes "github.com/cosmos/interchain-security/v5/x/ccv/types"
)

// getTemplateClient returns the template client for provider proposals
func getTemplateClient(ctx sdk.Context, paramSpace ccvtypes.LegacyParamSubspace) *ibctmtypes.ClientState {
	var cs ibctmtypes.ClientState
	paramSpace.Get(ctx, types.KeyTemplateClient, &cs)
	return &cs
}

// getTrustingPeriodFraction returns a TrustingPeriodFraction
// used to compute the provider IBC client's TrustingPeriod as UnbondingPeriod / TrustingPeriodFraction
func getTrustingPeriodFraction(ctx sdk.Context, paramSpace ccvtypes.LegacyParamSubspace) string {
	var f string
	paramSpace.Get(ctx, types.KeyTrustingPeriodFraction, &f)
	return f
}

// getCCVTimeoutPeriod returns the timeout period for sent ibc packets
func getCCVTimeoutPeriod(ctx sdk.Context, paramSpace ccvtypes.LegacyParamSubspace) time.Duration {
	var p time.Duration
	paramSpace.Get(ctx, ccvtypes.KeyCCVTimeoutPeriod, &p)
	return p
}

// getSlashMeterReplenishPeriod returns the period in which:
// Once the slash meter becomes not-full, the slash meter is replenished after this period.
func getSlashMeterReplenishPeriod(ctx sdk.Context, paramSpace ccvtypes.LegacyParamSubspace) time.Duration {
	var p time.Duration
	paramSpace.Get(ctx, types.KeySlashMeterReplenishPeriod, &p)
	return p
}

// getSlashMeterReplenishFraction returns the string fraction of total voting power that is replenished
// to the slash meter every replenish period. This param also serves as a maximum fraction of total
// voting power that the slash meter can hold.
func getSlashMeterReplenishFraction(ctx sdk.Context, paramSpace ccvtypes.LegacyParamSubspace) string {
	var f string
	paramSpace.Get(ctx, types.KeySlashMeterReplenishFraction, &f)
	return f
}

func getConsumerRewardDenomRegistrationFee(ctx sdk.Context, paramSpace ccvtypes.LegacyParamSubspace) sdk.Coin {
	var c sdk.Coin
	paramSpace.Get(ctx, types.KeyConsumerRewardDenomRegistrationFee, &c)
	return c
}

func getBlocksPerEpoch(ctx sdk.Context, paramSpace ccvtypes.LegacyParamSubspace) int64 {
	var b int64
	paramSpace.Get(ctx, types.KeyBlocksPerEpoch, &b)
	return b
}

func getNumberOfEpochsToStartReceivingRewards(ctx sdk.Context, paramSpace ccvtypes.LegacyParamSubspace) int64 {
	var b int64
	paramSpace.Get(ctx, types.KeyNumberOfEpochsToStartReceivingRewards, &b)
	return b
}

// Legacy: Only for migration purposes. GetParamsLegacy returns the paramset for the provider
// module from a given param subspace
func GetParamsLegacy(ctx sdk.Context, paramspace ccvtypes.LegacyParamSubspace) types.Params {
	return types.NewParams(
		getTemplateClient(ctx, paramspace),
		getTrustingPeriodFraction(ctx, paramspace),
		getCCVTimeoutPeriod(ctx, paramspace),
		getSlashMeterReplenishPeriod(ctx, paramspace),
		getSlashMeterReplenishFraction(ctx, paramspace),
		getConsumerRewardDenomRegistrationFee(ctx, paramspace),
		getBlocksPerEpoch(ctx, paramspace),
		getNumberOfEpochsToStartReceivingRewards(ctx, paramspace),
	)
}
