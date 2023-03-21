package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	abci "github.com/tendermint/tendermint/abci/types"
)

func (k Keeper) ChangeoverIsComplete(ctx sdk.Context) bool {
	// TODO: confirm correctness here.
	return ctx.BlockHeight() >= k.FirstConsumerHeight(ctx)
}

// TODO: store this height directly in a better way when prov valset is used
func (k Keeper) FirstConsumerHeight(ctx sdk.Context) int64 {
	lastStandaloneHeight, found := k.GetLastStandaloneHeight(ctx)
	// If last standalone height not found, chain has always been consumer
	if !found {
		return 0
	}
	// Else first consumer height is 2 blocks after last standalone height
	return lastStandaloneHeight + 2
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
