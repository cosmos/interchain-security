package keeper_test

import (
	testkeeper "github.com/cosmos/interchain-security/v4/testutil/keeper"
	"github.com/stretchr/testify/require"
	"testing"
)

func TestHandleOptIn(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	valAddress := []byte("valAddr")

	// if validator (`valAddress`) is to be opted out, then we cancel that the validator is about
	// to be opted out and do not consider the validator to opt in
	providerKeeper.SetToBeOptedOut(ctx, "chainID", valAddress)
	require.True(t, providerKeeper.IsToBeOptedOut(ctx, "chainID", valAddress))
	providerKeeper.HandleOptIn(ctx, "chainID", valAddress, nil)
	require.False(t, providerKeeper.IsToBeOptedIn(ctx, "chainID", valAddress))
	require.False(t, providerKeeper.IsToBeOptedOut(ctx, "chainID", valAddress))

	// if validator (`valAddress`) is already opted in, then the validator cannot be opted in
	providerKeeper.SetOptedIn(ctx, "chainID", valAddress, 1)
	providerKeeper.HandleOptIn(ctx, "chainID", valAddress, nil)
	require.False(t, providerKeeper.IsToBeOptedIn(ctx, "chainID", valAddress))
}

func TestHandleOptOut(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	valAddress := []byte("valAddr")

	// if validator (`valAddress`) is to be opted in, then we cancel that the validator is about
	// to be opted out and do not consider the validator to opt out
	providerKeeper.SetToBeOptedIn(ctx, "chainID", valAddress)
	require.True(t, providerKeeper.IsToBeOptedIn(ctx, "chainID", valAddress))
	providerKeeper.HandleOptOut(ctx, "chainID", valAddress)
	require.False(t, providerKeeper.IsToBeOptedOut(ctx, "chainID", valAddress))
	require.False(t, providerKeeper.IsToBeOptedIn(ctx, "chainID", valAddress))

	// if validator (`valAddress`) is not opted in, then the validator cannot be opted out
	providerKeeper.DeleteOptedIn(ctx, "chainID", valAddress)
	providerKeeper.HandleOptOut(ctx, "chainID", valAddress)
	require.False(t, providerKeeper.IsToBeOptedOut(ctx, "chainID", valAddress))
}
