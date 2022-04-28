package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"

	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"

	"github.com/cosmos/interchain-security/x/ccv/provider/types"
)

// GetTemplateClient returns the template client for provider proposals
func (k Keeper) GetTemplateClient(ctx sdk.Context) *ibctmtypes.ClientState {
	var cs ibctmtypes.ClientState
	k.paramSpace.Get(ctx, types.KeyTemplateClient, &cs)
	return &cs
}

// GetParams returns the paramset for the provider module
func (k Keeper) GetParams(ctx sdk.Context) types.Params {
	return types.NewParams(k.GetTemplateClient(ctx))
}

// SetParams sets the paramset for the provider module
func (k Keeper) SetParams(ctx sdk.Context, params types.Params) {
	k.paramSpace.SetParamSet(ctx, &params)
}
