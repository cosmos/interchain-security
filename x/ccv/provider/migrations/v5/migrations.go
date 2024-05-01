package v5

import (
	sdk "github.com/cosmos/cosmos-sdk/types"

	providerkeeper "github.com/cosmos/interchain-security/v5/x/ccv/provider/keeper"
)

// This migration only takes already registered chains into account.
// If a chain is in voting while the upgrade happens, this is not sufficient,
// and a migration to rewrite the proposal is needed.
func MigrateTopNForRegisteredChains(ctx sdk.Context, providerKeeper providerkeeper.Keeper) {
	// get all consumer chains
	registeredConsumerChains := providerKeeper.GetAllConsumerChains(ctx)

	// Set the topN of each chain to 95
	for _, chain := range registeredConsumerChains {
		providerKeeper.SetTopN(ctx, chain.ChainId, 95)
	}
}

// // If there are consumer addition proposals in the voting period at the upgrade time, they may need the topN value updated.
// func MigrateTopNForVotingPeriodChains(ctx sdk.Context, govKeeper govkeeper.Keeper, providerKeeper providerkeeper.Keeper) {
// }
