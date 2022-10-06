package keeper

import (
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"

	"github.com/cosmos/interchain-security/x/ccv/consumer/types"
)

// GetParams returns the paramset for the consumer module
func (k Keeper) GetParams(ctx sdk.Context) types.Params {
	return types.NewParams(
		k.GetEnabled(ctx),
		k.GetBlocksPerDistributionTransmission(ctx),
		k.GetDistributionTransmissionChannel(ctx),
		k.GetProviderFeePoolAddrStr(ctx),
		k.GetUnbondingPeriod(ctx),
	)
}

// TODO: make sure consumer unbonding period is validated

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

func (k Keeper) GetUnbondingPeriod(ctx sdk.Context) time.Duration {
	var period time.Duration
	k.paramStore.Get(ctx, types.KeyConsumerUnbondingPeriod, &period)
	return period
}
