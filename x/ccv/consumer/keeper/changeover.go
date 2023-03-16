package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	abci "github.com/tendermint/tendermint/abci/types"
)

func (k Keeper) ChangeoverToConsumer(ctx sdk.Context) (initialValUpdates []abci.ValidatorUpdate) {

	initialValUpdates = k.GetInitialValSet(ctx)
	// set last sovereign height
	k.SetLastSovereignHeight(ctx, ctx.BlockHeight())
	// populate cross chain validators states with initial valset
	k.ApplyCCValidatorChanges(ctx, initialValUpdates)

	// Add validator updates to initialValUpdates, such that the "old" validators returned from sovereign staking module
	// are given zero power, and the "new" validators are given their full power.
	initialUpdatesFlag := make(map[string]bool)
	for _, val := range initialValUpdates {
		initialUpdatesFlag[val.PubKey.String()] = true
	}
	for _, val := range k.GetLastSovereignValidators(ctx) {
		zeroPowerUpdate := val.ABCIValidatorUpdateZero()
		if !initialUpdatesFlag[zeroPowerUpdate.PubKey.String()] {
			initialValUpdates = append(initialValUpdates, zeroPowerUpdate)
		}
	}

	// Note: validator set update is only done on consumer chain from first endblocker
	// on soft fork from existing chain
	k.DeletePreCCV(ctx)

	return initialValUpdates
}
