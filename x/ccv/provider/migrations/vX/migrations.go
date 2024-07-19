package v6

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	providerkeeper "github.com/cosmos/interchain-security/v5/x/ccv/provider/keeper"
)

// InitializeMaxValidatorsForExistingConsumers initializes the max validators
// parameter for existing consumers to the MaxProviderConsensusValidators parameter.
// This is necessary to avoid those consumer chains having an excessive amount of validators.
func InitializeMaxValidatorsForExistingConsumers(ctx sdk.Context, providerKeeper providerkeeper.Keeper) {
	maxVals := providerKeeper.GetParams(ctx).MaxProviderConsensusValidators
	for _, chainID := range providerKeeper.GetAllRegisteredConsumerChainIDs(ctx) {
		providerKeeper.SetValidatorSetCap(ctx, chainID, uint32(maxVals))
	}
}

// InitializeAllowInactiveVals initializes the allow inactive validators parameter to be false
// for all existing consumer chains.
func InitializeAllowInactiveVals(ctx sdk.Context, providerKeeper providerkeeper.Keeper) {
	for _, chainID := range providerKeeper.GetAllRegisteredConsumerChainIDs(ctx) {
		providerKeeper.SetAllowInactiveValidators(ctx, chainID, false)
	}
}
