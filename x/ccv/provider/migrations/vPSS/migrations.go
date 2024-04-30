package vPSS

import (
	sdk "github.com/cosmos/cosmos-sdk/types"

	stakingkeeper "github.com/cosmos/cosmos-sdk/x/staking/keeper"
	providerkeeper "github.com/cosmos/interchain-security/v4/x/ccv/provider/keeper"
)

// This migration only takes already registered chains into account.
// If a chain is in voting while the upgrade happens, this is not sufficient,
// and a migration to rewrite the proposal is needed.
func MigrateTopNForRegisteredChains(ctx sdk.Context, providerKeeper providerkeeper.Keeper, stakingKeeper stakingkeeper.Keeper) {
	// get all consumer chains
	registeredConsumerChains := providerKeeper.GetAllConsumerChains(ctx)

	for _, chain := range registeredConsumerChains {
		// Set the topN of each chain to 95
		providerKeeper.SetTopN(ctx, chain.ChainId, 95)

		// set the minimal power in the top N
		bondedValidators := stakingKeeper.GetLastValidators(ctx)
		minPower := providerKeeper.ComputeMinPowerInTopN(ctx, chain.ChainId, bondedValidators, 95)
		providerKeeper.SetMinimumPowerInTopN(ctx, chain.ChainId, minPower)
	}
}

// // If there are consumer addition proposals in the voting period at the upgrade time, they may need the topN value updated.
// func MigrateTopNForVotingPeriodChains(ctx sdk.Context, govKeeper govkeeper.Keeper, providerKeeper providerkeeper.Keeper) {
// }
