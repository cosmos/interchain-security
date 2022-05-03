package keeper

import (
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
		k.GetConsumerRedistributeFrac(ctx),
	)
}

// SetParams sets the paramset for the consumer module
func (k Keeper) SetParams(ctx sdk.Context, params types.Params) {
	k.paramSpace.SetParamSet(ctx, &params)
}

// GetEnabled returns the enabled flag for the consumer module
func (k Keeper) GetEnabled(ctx sdk.Context) bool {
	var enabled bool
	k.paramSpace.Get(ctx, types.KeyEnabled, &enabled)
	return enabled
}

func (k Keeper) GetBlocksPerDistributionTransmission(ctx sdk.Context) int64 {
	var bpdt int64
	k.paramSpace.Get(ctx, types.KeyBlocksPerDistributionTransmission, &bpdt)
	return bpdt
}

func (k Keeper) SetBlocksPerDistributionTransmission(ctx sdk.Context, bpdt int64) {
	k.paramSpace.Set(ctx, types.KeyBlocksPerDistributionTransmission, bpdt)
}

func (k Keeper) GetDistributionTransmissionChannel(ctx sdk.Context) string {
	var s string
	k.paramSpace.Get(ctx, types.KeyDistributionTransmissionChannel, &s)
	return s
}

func (k Keeper) SetDistributionTransmissionChannel(ctx sdk.Context, channel string) {
	k.paramSpace.Set(ctx, types.KeyDistributionTransmissionChannel, channel)
}

func (k Keeper) GetProviderFeePoolAddrStr(ctx sdk.Context) string {
	var s string
	k.paramSpace.Get(ctx, types.KeyProviderFeePoolAddrStr, &s)
	return s
}

func (k Keeper) SetProviderFeePoolAddrStr(ctx sdk.Context, addr string) {
	k.paramSpace.Set(ctx, types.KeyProviderFeePoolAddrStr, addr)
}

func (k Keeper) GetConsumerRedistributeFrac(ctx sdk.Context) string {
	var s string
	k.paramSpace.Get(ctx, types.KeyConsumerRedistributeFrac, &s)
	return s
}

func (k Keeper) SetConsumerRedistributeFrac(ctx sdk.Context, fracStr string) {
	k.paramSpace.Set(ctx, types.KeyConsumerRedistributeFrac, fracStr)
}
