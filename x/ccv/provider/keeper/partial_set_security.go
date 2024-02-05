package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
)

type OptedInValidator struct {
	ProviderAddr types.ProviderConsAddress
	// block height the validator opted in at
	BlockHeight uint64
}

func (k Keeper) HandleOptIn(ctx sdk.Context, chainID string, providerAddr types.ProviderConsAddress) {
	if k.IsToBeOptedOut(ctx, chainID, providerAddr) {
		k.DeleteToBeOptedOut(ctx, chainID, providerAddr)
	} else if !k.IsToBeOptedIn(ctx, chainID, providerAddr) && !k.IsOptedIn(ctx, chainID, providerAddr) {
		k.SetToBeOptedIn(ctx, chainID, providerAddr)
	}
}

func (k Keeper) HandleOptOut(ctx sdk.Context, chainID string, providerAddr types.ProviderConsAddress) {
	if k.IsToBeOptedIn(ctx, chainID, providerAddr) {
		k.DeleteToBeOptedIn(ctx, chainID, providerAddr)
	} else if !k.IsToBeOptedOut(ctx, chainID, providerAddr) && k.IsOptedIn(ctx, chainID, providerAddr) {
		k.SetToBeOptedOut(ctx, chainID, providerAddr)
	}
}
