package keeper

import (
	errorsmod "cosmossdk.io/errors"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
)

type OptedInValidator struct {
	ProviderAddr types.ProviderConsAddress
	// block height the validator opted in at
	BlockHeight uint64
}

func (k Keeper) HandleOptIn(ctx sdk.Context, chainID string, providerAddr types.ProviderConsAddress, consumerKey *string) error {
	if !k.IsConsumerProposedOrRegistered(ctx, chainID) {
		return errorsmod.Wrapf(
			types.ErrUnknownConsumerChainId,
			"opting in to an unknown consumer chain id: %s", chainID)
	}

	if k.IsToBeOptedOut(ctx, chainID, providerAddr) {
		// a validator to be opted in cancels out with a validator to be opted out
		k.DeleteToBeOptedOut(ctx, chainID, providerAddr)
	} else if !k.IsToBeOptedIn(ctx, chainID, providerAddr) && !k.IsOptedIn(ctx, chainID, providerAddr) {
		// a validator can only be set for opt in if it is not opted in and not already set for opt in
		k.SetToBeOptedIn(ctx, chainID, providerAddr)
	}

	if consumerKey != nil {
		// TODO (PR 1586): assign consumer key in this case
	}

	return nil
}

func (k Keeper) HandleOptOut(ctx sdk.Context, chainID string, providerAddr types.ProviderConsAddress) error {
	if !k.IsConsumerProposedOrRegistered(ctx, chainID) {
		return errorsmod.Wrapf(
			types.ErrUnknownConsumerChainId,
			"opting out of an unknown consumer chain id: %s", chainID)
	}

	if k.IsToBeOptedIn(ctx, chainID, providerAddr) {
		// a validator to be opted out cancels out a validator to be opted in
		k.DeleteToBeOptedIn(ctx, chainID, providerAddr)
	} else if !k.IsToBeOptedOut(ctx, chainID, providerAddr) && k.IsOptedIn(ctx, chainID, providerAddr) {
		// a validator can only be set for opt out if it is opted in and not already set for opt out
		k.SetToBeOptedOut(ctx, chainID, providerAddr)
	}

	return nil
}
