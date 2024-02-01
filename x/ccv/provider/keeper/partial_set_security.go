package keeper

import (
	"fmt"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
)

// TODO: HandleOptIn
func (k Keeper) HandleOptIn(ctx sdk.Context, chainID string, providerAddr types.ProviderConsAddress) error {
	logger := k.Logger(ctx)

	if k.IsToBeOptedOut(ctx, chainID, providerAddr) {
		k.RemoveToBeOptedOut(ctx, chainID, providerAddr)
		return nil
	} else if k.IsToBeOptedIn(ctx, chainID, providerAddr) {
		return nil
	} else if k.IsOptedIn(ctx, chainID, providerAddr) {
		logger.Error("That's a big no")
		return fmt.Errorf("What's happening? already opted in")
	} else {
		k.SetToBeOptedIn(ctx, chainID, providerAddr)
	}

	//if msg.GetConsumerKey() != "" {
	//  k.AssignConsumerKey(ctx, msg.ChainId)
	//}

	return nil
}

func (k Keeper) HandleOptOut(ctx sdk.Context, chainID string, providerAddr types.ProviderConsAddress) error {
	logger := k.Logger(ctx)

	if k.IsToBeOptedIn(ctx, chainID, providerAddr) {
		k.RemoveToBeOptedIn(ctx, chainID, providerAddr)
		return nil
	} else if k.IsToBeOptedOut(ctx, chainID, providerAddr) {
		return nil
	} else if !k.IsOptedIn(ctx, chainID, providerAddr) {
		logger.Error("that's a no!")
		return fmt.Errorf("What's happening? already opted in")
	} else {
		k.SetToBeOptedOut(ctx, chainID, providerAddr)
	}

	return nil
}
