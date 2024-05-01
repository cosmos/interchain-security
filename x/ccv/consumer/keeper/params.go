package keeper

import (
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	ccvtypes "github.com/cosmos/interchain-security/v5/x/ccv/types"
)

// GetParams returns the params for the consumer ccv module
// NOTE: it is different from the GetParams method which is required to implement StakingKeeper interface
func (k Keeper) GetConsumerParams(ctx sdk.Context) ccvtypes.ConsumerParams {
	return ccvtypes.NewParams(
		k.GetEnabled(ctx),
		k.GetBlocksPerDistributionTransmission(ctx),
		k.GetDistributionTransmissionChannel(ctx),
		k.GetProviderFeePoolAddrStr(ctx),
		k.GetCCVTimeoutPeriod(ctx),
		k.GetTransferTimeoutPeriod(ctx),
		k.GetConsumerRedistributionFrac(ctx),
		k.GetHistoricalEntries(ctx),
		k.GetUnbondingPeriod(ctx),
		k.GetSoftOptOutThreshold(ctx),
		k.GetRewardDenoms(ctx),
		k.GetProviderRewardDenoms(ctx),
		k.GetRetryDelayPeriod(ctx),
	)
}

// SetParams sets the paramset for the consumer module
func (k Keeper) SetParams(ctx sdk.Context, params ccvtypes.ConsumerParams) {
	k.paramStore.SetParamSet(ctx, &params)
}

// GetParams implements StakingKeeper GetParams interface method
// it returns an a empty stakingtypes.Params struct
// NOTE: this method must be implemented on the consumer keeper because the evidence module keeper
// in cosmos-sdk v0.47 requires this exact method with this exact signature to be available on the StakingKeepr
func (k Keeper) GetParams(ctx sdk.Context) stakingtypes.Params {
	return stakingtypes.Params{}
}

// GetEnabled returns the enabled flag for the consumer module
func (k Keeper) GetEnabled(ctx sdk.Context) bool {
	var enabled bool
	k.paramStore.Get(ctx, ccvtypes.KeyEnabled, &enabled)
	return enabled
}

func (k Keeper) GetBlocksPerDistributionTransmission(ctx sdk.Context) int64 {
	var bpdt int64
	k.paramStore.Get(ctx, ccvtypes.KeyBlocksPerDistributionTransmission, &bpdt)
	return bpdt
}

func (k Keeper) SetBlocksPerDistributionTransmission(ctx sdk.Context, bpdt int64) {
	k.paramStore.Set(ctx, ccvtypes.KeyBlocksPerDistributionTransmission, bpdt)
}

func (k Keeper) GetDistributionTransmissionChannel(ctx sdk.Context) string {
	var s string
	k.paramStore.Get(ctx, ccvtypes.KeyDistributionTransmissionChannel, &s)
	return s
}

func (k Keeper) SetDistributionTransmissionChannel(ctx sdk.Context, channel string) {
	k.paramStore.Set(ctx, ccvtypes.KeyDistributionTransmissionChannel, channel)
}

func (k Keeper) GetProviderFeePoolAddrStr(ctx sdk.Context) string {
	var s string
	k.paramStore.Get(ctx, ccvtypes.KeyProviderFeePoolAddrStr, &s)
	return s
}

func (k Keeper) SetProviderFeePoolAddrStr(ctx sdk.Context, addr string) {
	k.paramStore.Set(ctx, ccvtypes.KeyProviderFeePoolAddrStr, addr)
}

// GetCCVTimeoutPeriod returns the timeout period for sent ccv related ibc packets
func (k Keeper) GetCCVTimeoutPeriod(ctx sdk.Context) time.Duration {
	var p time.Duration
	k.paramStore.Get(ctx, ccvtypes.KeyCCVTimeoutPeriod, &p)
	return p
}

// GetTransferTimeoutPeriod returns the timeout period for sent transfer related ibc packets
func (k Keeper) GetTransferTimeoutPeriod(ctx sdk.Context) time.Duration {
	var p time.Duration
	k.paramStore.Get(ctx, ccvtypes.KeyTransferTimeoutPeriod, &p)
	return p
}

// GetConsumerRedistributionFrac returns the fraction of tokens allocated to the consumer redistribution
// address during distribution events. The fraction is a string representing a
// decimal number. For example "0.75" would represent 75%.
func (k Keeper) GetConsumerRedistributionFrac(ctx sdk.Context) string {
	var str string
	k.paramStore.Get(ctx, ccvtypes.KeyConsumerRedistributionFrac, &str)
	return str
}

// GetHistoricalEntries returns the number of historical info entries to persist in store
func (k Keeper) GetHistoricalEntries(ctx sdk.Context) int64 {
	var n int64
	k.paramStore.Get(ctx, ccvtypes.KeyHistoricalEntries, &n)
	return n
}

// Only used to set an unbonding period in diff tests
func (k Keeper) SetUnbondingPeriod(ctx sdk.Context, period time.Duration) {
	k.paramStore.Set(ctx, ccvtypes.KeyConsumerUnbondingPeriod, period)
}

func (k Keeper) GetUnbondingPeriod(ctx sdk.Context) time.Duration {
	var period time.Duration
	k.paramStore.Get(ctx, ccvtypes.KeyConsumerUnbondingPeriod, &period)
	return period
}

// GetSoftOptOutThreshold returns the percentage of validators at the bottom of the set
// that can opt out of running the consumer chain
func (k Keeper) GetSoftOptOutThreshold(ctx sdk.Context) string {
	var str string
	k.paramStore.Get(ctx, ccvtypes.KeySoftOptOutThreshold, &str)
	return str
}

func (k Keeper) GetRewardDenoms(ctx sdk.Context) []string {
	var denoms []string
	k.paramStore.Get(ctx, ccvtypes.KeyRewardDenoms, &denoms)
	return denoms
}

func (k Keeper) GetProviderRewardDenoms(ctx sdk.Context) []string {
	var denoms []string
	k.paramStore.Get(ctx, ccvtypes.KeyProviderRewardDenoms, &denoms)
	return denoms
}

func (k Keeper) GetRetryDelayPeriod(ctx sdk.Context) time.Duration {
	var period time.Duration
	k.paramStore.Get(ctx, ccvtypes.KeyRetryDelayPeriod, &period)
	return period
}
