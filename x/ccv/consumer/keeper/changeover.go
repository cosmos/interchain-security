package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"

	abci "github.com/cometbft/cometbft/abci/types"
)

// ChangeoverIsComplete returns whether the standalone to consumer changeover process is complete.
func (k Keeper) ChangeoverIsComplete(ctx sdk.Context) bool {
	if !k.IsPrevStandaloneChain(ctx) {
		panic("ChangeoverIsComplete should only be called on previously standalone consumers")
	}
	return ctx.BlockHeight() >= k.FirstConsumerHeight(ctx)
}

// FirstConsumerHeight returns the first height that the ccv valset will be in effect is 2 blocks after init genesis height
// (aka height that the ccv module first returned updates to tendermint), because if init genesis is block N,
// the new valset is committed in block N+ValidatorUpdateDelay, and in effect for block N+ValidatorUpdateDelay+1.
func (k Keeper) FirstConsumerHeight(ctx sdk.Context) int64 {
	return k.GetInitGenesisHeight(ctx) + sdk.ValidatorUpdateDelay + 1
}

// ChangeoverToConsumer includes the logic that needs to execute during the process of a
// standalone to consumer changeover, where the previously standalone chain has
// just been upgraded to include the consumer ccv module, but the provider valset is not
// yet responsible for POS/block production. This method constructs validator updates
// that will be given to tendermint, which allows the consumer chain to
// start using the provider valset, while the standalone valset is given zero voting power where appropriate.
func (k Keeper) ChangeoverToConsumer(ctx sdk.Context) (initialValUpdates []abci.ValidatorUpdate) {
	// populate cross chain validators states with initial valset
	initialValUpdates = k.GetInitialValSet(ctx)
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

	k.Logger(ctx).Info("ICS changeover complete - you are now a consumer chain!")
	return initialValUpdates
}
