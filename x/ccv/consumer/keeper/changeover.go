package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	abci "github.com/tendermint/tendermint/abci/types"
)

// TODO: tests around this logic
// ChangeoverIsComplete returns whether the standalone to consumer changeover process is complete.
func (k Keeper) ChangeoverIsComplete(ctx sdk.Context) bool {
	if !k.IsPrevStandaloneChain() {
		panic("ChangeoverIsComplete should only be called on previously standalone consumers")
	}
	return ctx.BlockHeight() >= k.FirstConsumerHeight(ctx)
}

// The first height that the ccv valset will be in effect is 2 blocks after last standalone height
// (aka height that the ccv module first returned updates to tendermint), because the new valset is committed
// in block N+1, and in effect for block N+2.
func (k Keeper) FirstConsumerHeight(ctx sdk.Context) int64 {
	return k.GetLastStandaloneHeight(ctx) + 2
}

// ChangeoverToConsumer includes the logic that needs to execute during the process of a
// standalone to consumer changeover, where the previously standalone chain has
// just been upgraded to include the consumer ccv module, but the provider valset is not
// yet responsible for POS/block production. This method constructs validator updates
// that will be given to tendermint, which allows the consumer chain to
// start using the provider valset, while the standalone valset is given zero voting power where appropriate.
func (k Keeper) ChangeoverToConsumer(ctx sdk.Context) (initialValUpdates []abci.ValidatorUpdate) {
	initialValUpdates = k.GetInitialValSet(ctx)
	// set last standalone height
	k.SetLastStandaloneHeight(ctx, ctx.BlockHeight())
	// populate cross chain validators states with initial valset
	k.ApplyCCValidatorChanges(ctx, initialValUpdates)

	// Add validator updates to initialValUpdates, such that the "old" validators returned from standalone staking module
	// are given zero power, and the provider validators are given their full power.
	initialUpdatesFlag := make(map[string]bool)
	for _, val := range initialValUpdates {
		initialUpdatesFlag[val.PubKey.String()] = true
	}
	for _, val := range k.GetLastStandaloneValidators(ctx) {
		zeroPowerUpdate := val.ABCIValidatorUpdateZero()
		if !initialUpdatesFlag[zeroPowerUpdate.PubKey.String()] {
			initialValUpdates = append(initialValUpdates, zeroPowerUpdate)
		}
	}

	// Note: this method should only be executed once as a part of the changeover process.
	// Therefore we set the PreCCV state to false so the endblocker caller doesn't call this method again.
	k.DeletePreCCV(ctx)

	return initialValUpdates
}
