package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"

	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"

	"github.com/cosmos/interchain-security/x/ccv/parent/types"
)

// GetTemplateClient returns the template client for parent proposals
func (k Keeper) GetTemplateClient(ctx sdk.Context) *ibctmtypes.ClientState {
	var cs ibctmtypes.ClientState
	k.paramSpace.Get(ctx, types.KeyTemplateClient, &cs)
	return &cs
}

// GetParams returns the paramset for the parent module
func (k Keeper) GetParams(ctx sdk.Context) types.Params {
	return types.NewParams(k.GetTemplateClient(ctx))
}

// SetParams sets the paramset for the parent module
func (k Keeper) SetParams(ctx sdk.Context, params types.Params) {
	k.paramSpace.SetParamSet(ctx, &params)
}
