package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"

	"github.com/cosmos/interchain-security/x/ccv/child/types"
)

// GetEnabled returns the enabled flag for the child module
func (k Keeper) GetEnabled(ctx sdk.Context) bool {
	var enabled bool
	k.paramSpace.Get(ctx, types.KeyEnabled, &enabled)
	return enabled
}

// GetParams returns the paramset for the child module
func (k Keeper) GetParams(ctx sdk.Context) types.Params {
	return types.NewParams(k.GetEnabled(ctx))
}

// SetParams sets the paramset for the child module
func (k Keeper) SetParams(ctx sdk.Context, params types.Params) {
	k.paramSpace.SetParamSet(ctx, &params)
}
