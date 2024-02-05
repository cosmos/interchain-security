package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
)

type OptedInValidator struct {
	ValAddress sdk.ValAddress
	// block height the validator opted in at
	BlockHeight uint64
}

func (k Keeper) HandleOptIn(ctx sdk.Context, chainID string, valAddress sdk.ValAddress, consumerKey *string) {
	if k.IsToBeOptedOut(ctx, chainID, valAddress) {
		// a validator to be opted in cancels out with a validator to be opted out
		k.DeleteToBeOptedOut(ctx, chainID, valAddress)
	} else if !k.IsToBeOptedIn(ctx, chainID, valAddress) && !k.IsOptedIn(ctx, chainID, valAddress) {
		// a validator can only be set for opt in if it is not opted in and not already set for opt in
		k.SetToBeOptedIn(ctx, chainID, valAddress)
	}

	if consumerKey != nil {
		// TODO: assign consumer key in this case
	}
}

func (k Keeper) HandleOptOut(ctx sdk.Context, chainID string, valAddress sdk.ValAddress) {
	if k.IsToBeOptedIn(ctx, chainID, valAddress) {
		// a validator to be opted out cancels out a validator to be opted in
		k.DeleteToBeOptedIn(ctx, chainID, valAddress)
	} else if !k.IsToBeOptedOut(ctx, chainID, valAddress) && k.IsOptedIn(ctx, chainID, valAddress) {
		// a validator can only be set for opt out if it is opted in and not already set for opt out
		k.SetToBeOptedOut(ctx, chainID, valAddress)
	}
}
