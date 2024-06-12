package v6

import (
	sdk "github.com/cosmos/cosmos-sdk/types"

	stakingkeeper "github.com/cosmos/cosmos-sdk/x/staking/keeper"
	providerkeeper "github.com/cosmos/interchain-security/v4/x/ccv/provider/keeper"
)

func MigrateMinPowerInTopN(ctx sdk.Context, providerKeeper providerkeeper.Keeper, stakingKeeper stakingkeeper.Keeper) {
	// get all consumer chains
	registeredConsumerChains := providerKeeper.GetAllRegisteredConsumerChainIDs(ctx)

	for _, chain := range registeredConsumerChains {
		// get the top N
		topN, found := providerKeeper.GetTopN(ctx, chain)
		if !found {
			providerKeeper.Logger(ctx).Error("failed to get top N", "chain", chain)
			continue
		} else if topN == 0 {
			providerKeeper.Logger(ctx).Info("top N is 0, not setting minimal power", "chain", chain)
		} else {
			// set the minimal power in the top N
			bondedValidators := stakingKeeper.GetLastValidators(ctx)
			minPower, err := providerKeeper.ComputeMinPowerInTopN(ctx, bondedValidators, topN)
			if err != nil {
				providerKeeper.Logger(ctx).Error("failed to compute min power in top N", "chain", chain, "topN", topN, "error", err)
				continue
			}
			providerKeeper.SetMinimumPowerInTopN(ctx, chain, minPower)
		}
	}
}
