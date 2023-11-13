package keeper

import (
	"time"

	ibctmtypes "github.com/cosmos/ibc-go/v8/modules/light-clients/07-tendermint"

	sdk "github.com/cosmos/cosmos-sdk/types"

	"github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
)

// GetTemplateClient returns the template client for provider proposals
func (k Keeper) GetTemplateClient(ctx sdk.Context) *ibctmtypes.ClientState {
	params, err := k.GetParams(ctx)
	if err != nil {
		k.Logger(ctx).Error("error getting parameter 'TemplateClient': %v", err)
		return types.Params{}.TemplateClient
	}
	return params.TemplateClient
}

// GetTrustingPeriodFraction returns a TrustingPeriodFraction
// used to compute the provider IBC client's TrustingPeriod as UnbondingPeriod / TrustingPeriodFraction
func (k Keeper) GetTrustingPeriodFraction(ctx sdk.Context) string {
	params, err := k.GetParams(ctx)
	if err != nil {
		k.Logger(ctx).Error("error getting parameter 'TrustingPeriodFraction': %v", err)
		return types.Params{}.TrustingPeriodFraction
	}
	return params.TrustingPeriodFraction

}

// GetCCVTimeoutPeriod returns the timeout period for sent ibc packets
func (k Keeper) GetCCVTimeoutPeriod(ctx sdk.Context) time.Duration {
	params, err := k.GetParams(ctx)
	if err != nil {
		k.Logger(ctx).Error("error getting parameter 'CcvTimeoutPeriod': %v", err)
		return types.Params{}.CcvTimeoutPeriod
	}
	return params.CcvTimeoutPeriod
}

// GetInitTimeoutPeriod returns the init timeout period
func (k Keeper) GetInitTimeoutPeriod(ctx sdk.Context) time.Duration {
	params, err := k.GetParams(ctx)
	if err != nil {
		k.Logger(ctx).Error("error getting parameter 'InitTimeoutPeriod': %v", err)
		return types.Params{}.InitTimeoutPeriod
	}
	return params.InitTimeoutPeriod
}

// GetVscTimeoutPeriod returns the vsc timeout period
func (k Keeper) GetVscTimeoutPeriod(ctx sdk.Context) time.Duration {
	params, err := k.GetParams(ctx)
	if err != nil {
		k.Logger(ctx).Error("error getting parameter 'VscTimeoutPeriod': %v", err)
		return types.Params{}.VscTimeoutPeriod
	}
	return params.VscTimeoutPeriod
}

// SetVscTimeoutPeriod sets the vsc timeout period
func (k Keeper) SetVscTimeoutPeriod(ctx sdk.Context, period time.Duration) {
	params, err := k.GetParams(ctx)
	if err != nil {
		k.Logger(ctx).Error("error setting parameter 'VscTimeoutPeriod': %v", err)
		return
	}
	params.VscTimeoutPeriod = period
	k.SetParams(ctx, params)
}

// GetSlashMeterReplenishPeriod returns the period in which:
// Once the slash meter becomes not-full, the slash meter is replenished after this period.
func (k Keeper) GetSlashMeterReplenishPeriod(ctx sdk.Context) time.Duration {
	params, err := k.GetParams(ctx)
	if err != nil {
		k.Logger(ctx).Error("error getting parameter 'SlashMeterReplenishPeriod': %v", err)
		return types.Params{}.SlashMeterReplenishPeriod
	}
	return params.SlashMeterReplenishPeriod
}

// GetSlashMeterReplenishFraction returns the string fraction of total voting power that is replenished
// to the slash meter every replenish period. This param also serves as a maximum fraction of total
// voting power that the slash meter can hold.
func (k Keeper) GetSlashMeterReplenishFraction(ctx sdk.Context) string {
	params, err := k.GetParams(ctx)
	if err != nil {
		k.Logger(ctx).Error("error getting parameter 'SlashMeterReplenishFraction': %v", err)
		return types.Params{}.SlashMeterReplenishFraction
	}
	return params.SlashMeterReplenishFraction
}

// GetMaxThrottledPackets returns the maximum amount of throttled slash or vsc matured packets
// that can be queued for a single consumer before the provider chain halts.
func (k Keeper) GetMaxThrottledPackets(ctx sdk.Context) int64 {
	params, err := k.GetParams(ctx)
	if err != nil {
		k.Logger(ctx).Error("error getting parameter 'MaxThrottledPackets': %v", err)
		return types.Params{}.MaxThrottledPackets
	}
	return params.MaxThrottledPackets
}

func (k Keeper) GetConsumerRewardDenomRegistrationFee(ctx sdk.Context) sdk.Coin {
	// Due to difficulties doing migrations in coordinated upgrades, this param is hardcoded to 10 ATOM in v1.1.0-multiden.
	// The below code is the proper way to store the param. A future scheduled upgrade will
	// need to run migrations to add the param. This will allow us to change the fee by governance.
	params, err := k.GetParams(ctx)
	if err != nil {
		k.Logger(ctx).Error("error getting parameter 'ConsumerRewardDenomRegistrationFee': %v", err)
		return types.Params{}.ConsumerRewardDenomRegistrationFee
	}
	return params.ConsumerRewardDenomRegistrationFee
}

// GetParams returns the parameters for the provider module
func (k Keeper) GetParams(ctx sdk.Context) (types.Params, error) {
	store := k.storeService.OpenKVStore(ctx)
	bz, err := store.Get(types.ParametersKey())
	if err != nil {
		k.Logger(ctx).Error("error getting module parameters: %v", err)
		return types.Params{}, nil //TODO @bermuell: check if default arguments or error handling should be done
	}
	var params types.Params
	err = k.cdc.Unmarshal(bz, &params)
	return params, err
}

// SetParams sets the params for the provider module
func (k Keeper) SetParams(ctx sdk.Context, params types.Params) error {
	store := k.storeService.OpenKVStore(ctx)
	bz, err := k.cdc.Marshal(&params)
	if err != nil {
		return err
	}
	return store.Set(types.ParametersKey(), bz)
}
