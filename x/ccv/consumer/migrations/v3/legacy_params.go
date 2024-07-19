package v3

import (
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"

	ccvtypes "github.com/cosmos/interchain-security/v5/x/ccv/types"
)

// Legacy: used for migration only!
// GetConsumerParamsLegacy returns the params for the consumer ccv module from legacy subspace
func GetConsumerParamsLegacy(ctx sdk.Context, paramSpace ccvtypes.LegacyParamSubspace) ccvtypes.ConsumerParams {
	return ccvtypes.NewParams(
		getEnabled(ctx, paramSpace),
		getBlocksPerDistributionTransmission(ctx, paramSpace),
		getDistributionTransmissionChannel(ctx, paramSpace),
		getProviderFeePoolAddrStr(ctx, paramSpace),
		getCCVTimeoutPeriod(ctx, paramSpace),
		getTransferTimeoutPeriod(ctx, paramSpace),
		getConsumerRedistributionFrac(ctx, paramSpace),
		getHistoricalEntries(ctx, paramSpace),
		getUnbondingPeriod(ctx, paramSpace),
		getRewardDenoms(ctx, paramSpace),
		getProviderRewardDenoms(ctx, paramSpace),
		getRetryDelayPeriod(ctx, paramSpace),
	)
}

// getEnabled returns the enabled flag for the consumer module
func getEnabled(ctx sdk.Context, paramStore ccvtypes.LegacyParamSubspace) bool {
	var enabled bool
	paramStore.Get(ctx, ccvtypes.KeyEnabled, &enabled)
	return enabled
}

func getBlocksPerDistributionTransmission(ctx sdk.Context, paramStore ccvtypes.LegacyParamSubspace) int64 {
	var bpdt int64
	paramStore.Get(ctx, ccvtypes.KeyBlocksPerDistributionTransmission, &bpdt)
	return bpdt
}

func getDistributionTransmissionChannel(ctx sdk.Context, paramStore ccvtypes.LegacyParamSubspace) string {
	var s string
	paramStore.Get(ctx, ccvtypes.KeyDistributionTransmissionChannel, &s)
	return s
}

func getProviderFeePoolAddrStr(ctx sdk.Context, paramStore ccvtypes.LegacyParamSubspace) string {
	var s string
	paramStore.Get(ctx, ccvtypes.KeyProviderFeePoolAddrStr, &s)
	return s
}

// getCCVTimeoutPeriod returns the timeout period for sent ccv related ibc packets
func getCCVTimeoutPeriod(ctx sdk.Context, paramStore ccvtypes.LegacyParamSubspace) time.Duration {
	var p time.Duration
	paramStore.Get(ctx, ccvtypes.KeyCCVTimeoutPeriod, &p)
	return p
}

// getTransferTimeoutPeriod returns the timeout period for sent transfer related ibc packets
func getTransferTimeoutPeriod(ctx sdk.Context, paramStore ccvtypes.LegacyParamSubspace) time.Duration {
	var p time.Duration
	paramStore.Get(ctx, ccvtypes.KeyTransferTimeoutPeriod, &p)
	return p
}

// getConsumerRedistributionFrac returns the fraction of tokens allocated to the consumer redistribution
// address during distribution events. The fraction is a string representing a
// decimal number. For example "0.75" would represent 75%.
func getConsumerRedistributionFrac(ctx sdk.Context, paramStore ccvtypes.LegacyParamSubspace) string {
	var str string
	paramStore.Get(ctx, ccvtypes.KeyConsumerRedistributionFrac, &str)
	return str
}

// getHistoricalEntries returns the number of historical info entries to persist in store
func getHistoricalEntries(ctx sdk.Context, paramStore ccvtypes.LegacyParamSubspace) int64 {
	var n int64
	paramStore.Get(ctx, ccvtypes.KeyHistoricalEntries, &n)
	return n
}

func getUnbondingPeriod(ctx sdk.Context, paramStore ccvtypes.LegacyParamSubspace) time.Duration {
	var period time.Duration
	paramStore.Get(ctx, ccvtypes.KeyConsumerUnbondingPeriod, &period)
	return period
}

func getRewardDenoms(ctx sdk.Context, paramStore ccvtypes.LegacyParamSubspace) []string {
	var denoms []string
	paramStore.Get(ctx, ccvtypes.KeyRewardDenoms, &denoms)
	return denoms
}

func getProviderRewardDenoms(ctx sdk.Context, paramStore ccvtypes.LegacyParamSubspace) []string {
	var denoms []string
	paramStore.Get(ctx, ccvtypes.KeyProviderRewardDenoms, &denoms)
	return denoms
}

func getRetryDelayPeriod(ctx sdk.Context, paramStore ccvtypes.LegacyParamSubspace) time.Duration {
	var period time.Duration
	paramStore.Get(ctx, ccvtypes.KeyRetryDelayPeriod, &period)
	return period
}
