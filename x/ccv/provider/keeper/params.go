package keeper

import (
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"

	ibctmtypes "github.com/cosmos/ibc-go/v4/modules/light-clients/07-tendermint/types"

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
func (k Keeper) GetTrustingPeriodFraction(ctx sdk.Context) string {
	var f string
	k.paramSpace.Get(ctx, types.KeyTrustingPeriodFraction, &f)
	return f
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

// GetVscTimeoutPeriod returns the vsc timeout period
func (k Keeper) GetVscTimeoutPeriod(ctx sdk.Context) time.Duration {
	var p time.Duration
	k.paramSpace.Get(ctx, types.KeyVscTimeoutPeriod, &p)
	return p
}

// SetVscTimeoutPeriod sets the vsc timeout period
func (k Keeper) SetVscTimeoutPeriod(ctx sdk.Context, period time.Duration) {
	k.paramSpace.Set(ctx, types.KeyVscTimeoutPeriod, period)
}

// GetSlashMeterReplenishPeriod returns the period in which:
// Once the slash meter becomes not-full, the slash meter is replenished after this period.
func (k Keeper) GetSlashMeterReplenishPeriod(ctx sdk.Context) time.Duration {
	var p time.Duration
	k.paramSpace.Get(ctx, types.KeySlashMeterReplenishPeriod, &p)
	return p
}

// GetSlashMeterReplenishFraction returns the string fraction of total voting power that is replenished
// to the slash meter every replenish period. This param also serves as a maximum fraction of total
// voting power that the slash meter can hold.
func (k Keeper) GetSlashMeterReplenishFraction(ctx sdk.Context) string {
	var f string
	k.paramSpace.Get(ctx, types.KeySlashMeterReplenishFraction, &f)
	return f
}

// GetMaxThrottledPackets returns the maximum amount of throttled slash or vsc matured packets
// that can be queued for a single consumer before the provider chain halts.
func (k Keeper) GetMaxThrottledPackets(ctx sdk.Context) int64 {
	var p int64
	k.paramSpace.Get(ctx, types.KeyMaxThrottledPackets, &p)
	return p
}

func (k Keeper) GetConsumerRewardDenomRegistrationFee(ctx sdk.Context) sdk.Coin {
	// This should be a param, but due to difficulties adding params in migrations during coordinated upgrades,
	// we will hardcode the value for now. A future scheduled upgrade will change this to the above code and
	// run migrations to add the param. This will allow us to change the fee by governance, but for now it is set at 10 Atoms.
	return sdk.NewCoin(k.stakingKeeper.BondDenom(ctx), sdk.NewInt(10000000))
}

// GetParams returns the paramset for the provider module
func (k Keeper) GetParams(ctx sdk.Context) types.Params {
	return types.NewParams(
		k.GetTemplateClient(ctx),
		k.GetTrustingPeriodFraction(ctx),
		k.GetCCVTimeoutPeriod(ctx),
		k.GetInitTimeoutPeriod(ctx),
		k.GetVscTimeoutPeriod(ctx),
		k.GetSlashMeterReplenishPeriod(ctx),
		k.GetSlashMeterReplenishFraction(ctx),
		k.GetMaxThrottledPackets(ctx),
	)
}

// SetParams sets the params for the provider module
func (k Keeper) SetParams(ctx sdk.Context, params types.Params) {
	k.paramSpace.SetParamSet(ctx, &params)
}
