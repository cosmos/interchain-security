package keeper

import (
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"

	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"

	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"
)

// GetTemplateClient returns the template client for provider proposals
func (k Keeper) GetTemplateClient(ctx sdk.Context) *ibctmtypes.ClientState {
	var cs ibctmtypes.ClientState
	k.paramSpace.Get(ctx, types.KeyTemplateClient, &cs)
	return &cs
}

// GetTrustingPeriodFraction returns a TrustingPeriodFraction
// used to compute the provider IBC client's TrustingPeriod as UnbondingPeriod / TrustingPeriodFraction
func (k Keeper) GetTrustingPeriodFraction(ctx sdk.Context) int64 {
	var i int64
	k.paramSpace.Get(ctx, types.KeyTrustingPeriodFraction, &i)
	return i
}

// GetCCVTimeoutPeriod returns the timeout period for sent ibc packets
func (k Keeper) GetCCVTimeoutPeriod(ctx sdk.Context) time.Duration {
	var p time.Duration
	k.paramSpace.Get(ctx, ccvtypes.KeyCCVTimeoutPeriod, &p)
	return p
}

// GetInitTimeoutPeriod returns the init timeout period
func (k Keeper) GetInitTimeoutPeriod(ctx sdk.Context) time.Duration {
	var p time.Duration
	k.paramSpace.Get(ctx, types.KeyInitTimeoutPeriod, &p)
	return p
}

// GetSlashMeterReplenishPeriod returns the period for which the slash gas meter is replenished
func (k Keeper) GetSlashMeterReplenishPeriod(ctx sdk.Context) time.Duration {
	var p time.Duration
	k.paramSpace.Get(ctx, types.KeySlashMeterReplenishPeriod, &p)
	return p
}

// GetSlashGasReplenishFraction returns the string fraction of total voting power that is replenished to the
// slash gas meter every replenish period. This param also serves as a maximum fraction of total voting power
// that the slash gas meter can hold.
func (k Keeper) GetSlashGasReplenishFraction(ctx sdk.Context) string {
	var f string
	k.paramSpace.Get(ctx, types.KeySlashGasReplenishFraction, &f)
	return f
}

// GetMaxPendingSlashingPackets returns the maximum number of pending slashing packets that can be queued
// before the provider chain halts
func (k Keeper) GetMaxPendingSlashingPackets(ctx sdk.Context) int64 {
	var p int64
	k.paramSpace.Get(ctx, types.KeyMaxPendingSlashPackets, &p)
	return p
}

// GetParams returns the paramset for the provider module
func (k Keeper) GetParams(ctx sdk.Context) types.Params {
	return types.NewParams(
		k.GetTemplateClient(ctx),
		k.GetTrustingPeriodFraction(ctx),
		k.GetCCVTimeoutPeriod(ctx),
		k.GetInitTimeoutPeriod(ctx),
		k.GetSlashMeterReplenishPeriod(ctx),
		k.GetSlashGasReplenishFraction(ctx),
		k.GetMaxPendingSlashingPackets(ctx),
	)
}

// SetParams sets the params for the provider module
func (k Keeper) SetParams(ctx sdk.Context, params types.Params) {
	k.paramSpace.SetParamSet(ctx, &params)
}
