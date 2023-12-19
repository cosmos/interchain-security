package keeper

import (
	"fmt"
	"time"

	ibctmtypes "github.com/cosmos/ibc-go/v8/modules/light-clients/07-tendermint"

	sdk "github.com/cosmos/cosmos-sdk/types"

	"github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
)

// GetTemplateClient returns the template client for provider proposals
func (k Keeper) GetTemplateClient(ctx sdk.Context) *ibctmtypes.ClientState {
	params := k.GetParams(ctx)
	return params.TemplateClient
}

// GetTrustingPeriodFraction returns a TrustingPeriodFraction
// used to compute the provider IBC client's TrustingPeriod as UnbondingPeriod / TrustingPeriodFraction
func (k Keeper) GetTrustingPeriodFraction(ctx sdk.Context) string {
	params := k.GetParams(ctx)
	return params.TrustingPeriodFraction
}

// GetCCVTimeoutPeriod returns the timeout period for sent ibc packets
func (k Keeper) GetCCVTimeoutPeriod(ctx sdk.Context) time.Duration {
	params := k.GetParams(ctx)
	return params.CcvTimeoutPeriod
}

// GetInitTimeoutPeriod returns the init timeout period
func (k Keeper) GetInitTimeoutPeriod(ctx sdk.Context) time.Duration {
	params := k.GetParams(ctx)
	return params.InitTimeoutPeriod
}

// GetVscTimeoutPeriod returns the vsc timeout period
func (k Keeper) GetVscTimeoutPeriod(ctx sdk.Context) time.Duration {
	params := k.GetParams(ctx)
	return params.VscTimeoutPeriod
}

// SetVscTimeoutPeriod sets the vsc timeout period
func (k Keeper) SetVscTimeoutPeriod(ctx sdk.Context, period time.Duration) {
	params := k.GetParams(ctx)
	params.VscTimeoutPeriod = period
	k.SetParams(ctx, params)
}

// GetSlashMeterReplenishPeriod returns the period in which:
// Once the slash meter becomes not-full, the slash meter is replenished after this period.
func (k Keeper) GetSlashMeterReplenishPeriod(ctx sdk.Context) time.Duration {
	params := k.GetParams(ctx)
	return params.SlashMeterReplenishPeriod
}

// GetSlashMeterReplenishFraction returns the string fraction of total voting power that is replenished
// to the slash meter every replenish period. This param also serves as a maximum fraction of total
// voting power that the slash meter can hold.
func (k Keeper) GetSlashMeterReplenishFraction(ctx sdk.Context) string {
	params := k.GetParams(ctx)
	return params.SlashMeterReplenishFraction
}

func (k Keeper) GetConsumerRewardDenomRegistrationFee(ctx sdk.Context) sdk.Coin {
	// Due to difficulties doing migrations in coordinated upgrades, this param is hardcoded to 10 ATOM in v1.1.0-multiden.
	// The below code is the proper way to store the param. A future scheduled upgrade will
	// need to run migrations to add the param. This will allow us to change the fee by governance.
	params := k.GetParams(ctx)
	return params.ConsumerRewardDenomRegistrationFee
}

// GetParams returns the paramset for the provider module
func (k Keeper) GetParams(ctx sdk.Context) types.Params {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ParametersKey())
	var params types.Params
	err := k.cdc.Unmarshal(bz, &params)
	if err != nil {
		panic(fmt.Sprintf("error unmarshalling module parameters: %v:", err))
	}
	return params
}

// SetParams sets the params for the provider module
func (k Keeper) SetParams(ctx sdk.Context, params types.Params) {
	store := ctx.KVStore(k.storeKey)
	bz := k.cdc.MustMarshal(&params)
	store.Set(types.ParametersKey(), bz)
}
