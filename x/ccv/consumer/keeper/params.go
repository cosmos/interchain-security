package keeper

import (
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"

	"github.com/cosmos/interchain-security/x/ccv/consumer/types"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"
)

// GetParams returns the params for the consumer ccv module
func (k Keeper) GetParams(ctx sdk.Context) types.Params {
	return types.NewParams(
		k.GetEnabled(ctx),
		k.GetBlocksPerDistributionTransmission(ctx),
		k.GetDistributionTransmissionChannel(ctx),
		k.GetProviderFeePoolAddrStr(ctx),
		k.GetCCVTimeoutPeriod(ctx),
		k.GetTransferTimeoutPeriod(ctx),
		k.GetConsumerRedistributionFrac(ctx),
		k.GetHistoricalEntries(ctx),
		k.GetUnbondingPeriod(ctx),
	)
}

// SetParams sets the paramset for the consumer module
func (k Keeper) SetParams(ctx sdk.Context, params types.Params) {
	k.paramStore.SetParamSet(ctx, &params)
}

// GetEnabled returns the enabled flag for the consumer module
func (k Keeper) GetEnabled(ctx sdk.Context) bool {
	var enabled bool
	k.paramStore.Get(ctx, types.KeyEnabled, &enabled)
	return enabled
}

func (k Keeper) GetBlocksPerDistributionTransmission(ctx sdk.Context) int64 {
	var bpdt int64
	k.paramStore.Get(ctx, types.KeyBlocksPerDistributionTransmission, &bpdt)
	return bpdt
}

func (k Keeper) SetBlocksPerDistributionTransmission(ctx sdk.Context, bpdt int64) {
	k.paramStore.Set(ctx, types.KeyBlocksPerDistributionTransmission, bpdt)
}

func (k Keeper) GetDistributionTransmissionChannel(ctx sdk.Context) string {
	var s string
	k.paramStore.Get(ctx, types.KeyDistributionTransmissionChannel, &s)
	return s
}

func (k Keeper) SetDistributionTransmissionChannel(ctx sdk.Context, channel string) {
	k.paramStore.Set(ctx, types.KeyDistributionTransmissionChannel, channel)
}

func (k Keeper) GetProviderFeePoolAddrStr(ctx sdk.Context) string {
	var s string
	k.paramStore.Get(ctx, types.KeyProviderFeePoolAddrStr, &s)
	return s
}

func (k Keeper) SetProviderFeePoolAddrStr(ctx sdk.Context, addr string) {
	k.paramStore.Set(ctx, types.KeyProviderFeePoolAddrStr, addr)
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
	k.paramStore.Get(ctx, types.KeyTransferTimeoutPeriod, &p)
	return p
}

// GetConsumerRedistributionFrac returns the fraction of tokens allocated to the consumer redistribution
// address during distribution events. The fraction is a string representing a
// decimal number. For example "0.75" would represent 75%.
func (k Keeper) GetConsumerRedistributionFrac(ctx sdk.Context) string {
	var str string
	k.paramStore.Get(ctx, types.KeyConsumerRedistributionFrac, &str)
	return str
}

// GetHistoricalEntries returns the number of historical info entries to persist in store
func (k Keeper) GetHistoricalEntries(ctx sdk.Context) int64 {
	var n int64
	k.paramStore.Get(ctx, types.KeyHistoricalEntries, &n)
	return n
}

// Only used to set an unbonding period in diff tests
func (k Keeper) SetUnbondingPeriod(ctx sdk.Context, period time.Duration) {
	k.paramStore.Set(ctx, types.KeyConsumerUnbondingPeriod, period)
}

func (k Keeper) GetUnbondingPeriod(ctx sdk.Context) time.Duration {
	var period time.Duration
	k.paramStore.Get(ctx, types.KeyConsumerUnbondingPeriod, &period)
	return period
}
