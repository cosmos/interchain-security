package keeper

import (
	"time"

	ibctmtypes "github.com/cosmos/ibc-go/v8/modules/light-clients/07-tendermint"

	sdk "github.com/cosmos/cosmos-sdk/types"

	"github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v4/x/ccv/types"
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

func (k Keeper) GetConsumerRewardDenomRegistrationFee(ctx sdk.Context) sdk.Coin {
	// Due to difficulties doing migrations in coordinated upgrades, this param is hardcoded to 10 ATOM in v1.1.0-multiden.
	// The below code is the proper way to store the param. A future scheduled upgrade will
	// need to run migrations to add the param. This will allow us to change the fee by governance.
	var c sdk.Coin
	k.paramSpace.Get(ctx, types.KeyConsumerRewardDenomRegistrationFee, &c)
	return c
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
		k.GetConsumerRewardDenomRegistrationFee(ctx),
	)
}

// SetParams sets the params for the provider module
func (k Keeper) SetParams(ctx sdk.Context, params types.Params) {
	k.paramSpace.SetParamSet(ctx, &params)
}
