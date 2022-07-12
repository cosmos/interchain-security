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
		k.GetBaseProposerReward(ctx),
		k.GetBonusProposerReward(ctx),
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

// GetBaseProposerReward returns the current distribution base proposer rate.
func (k Keeper) GetBaseProposerReward(ctx sdk.Context) (percent sdk.Dec) {
	k.paramStore.Get(ctx, types.KeyParamStoreKeyBaseProposerReward, &percent)
	return percent
}

// GetBonusProposerReward returns the current distribution bonus proposer reward
// rate.
func (k Keeper) GetBonusProposerReward(ctx sdk.Context) (percent sdk.Dec) {
	k.paramStore.Get(ctx, types.KeyParamStoreKeyBonusProposerReward, &percent)
	return percent
}
