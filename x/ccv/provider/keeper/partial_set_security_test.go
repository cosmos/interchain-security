package keeper_test

import (
	testkeeper "github.com/cosmos/interchain-security/v4/testutil/keeper"
	"github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
	"github.com/stretchr/testify/require"
	"testing"
)

func TestHandleOptIn(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	providerAddr := types.NewProviderConsAddress([]byte("providerAddr"))

	// if validator (`providerAddr`) is to be opted out, then we cancel that the validator is about
	// to be opted out and do not consider the validator to opt in
	providerKeeper.SetToBeOptedOut(ctx, "chainID", providerAddr)
	require.True(t, providerKeeper.IsToBeOptedOut(ctx, "chainID", providerAddr))
	providerKeeper.HandleOptIn(ctx, "chainID", providerAddr)
	require.False(t, providerKeeper.IsToBeOptedIn(ctx, "chainID", providerAddr))
	require.False(t, providerKeeper.IsToBeOptedOut(ctx, "chainID", providerAddr))

	// if validator (`providerAddr`) is already opted in, then the validator cannot be opted in
	providerKeeper.SetOptedIn(ctx, "chainID", providerAddr, 1)
	providerKeeper.HandleOptIn(ctx, "chainID", providerAddr)
	require.False(t, providerKeeper.IsToBeOptedIn(ctx, "chainID", providerAddr))
}

func TestHandleOptOut(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	providerAddr := types.NewProviderConsAddress([]byte("providerAddr"))

	// if validator (`providerAddr`) is to be opted in, then we cancel that the validator is about
	// to be opted out and do not consider the validator to opt out
	providerKeeper.SetToBeOptedIn(ctx, "chainID", providerAddr)
	require.True(t, providerKeeper.IsToBeOptedIn(ctx, "chainID", providerAddr))
	providerKeeper.HandleOptOut(ctx, "chainID", providerAddr)
	require.False(t, providerKeeper.IsToBeOptedOut(ctx, "chainID", providerAddr))
	require.False(t, providerKeeper.IsToBeOptedIn(ctx, "chainID", providerAddr))

	// if validator (`providerAddr`) is not opted in, then the validator cannot be opted out
	providerKeeper.RemoveOptedIn(ctx, "chainID", providerAddr)
	providerKeeper.HandleOptOut(ctx, "chainID", providerAddr)
	require.False(t, providerKeeper.IsToBeOptedOut(ctx, "chainID", providerAddr))
}
