package v6

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"

	providerkeeper "github.com/cosmos/interchain-security/v5/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
)

// MigrateParams adds missing provider chain params to the param store.
func MigrateParams(ctx sdk.Context, paramsSubspace paramtypes.Subspace) {
	if !paramsSubspace.HasKeyTable() {
		paramsSubspace.WithKeyTable(providertypes.ParamKeyTable())
	}
	paramsSubspace.Set(ctx, providertypes.KeyNumberOfEpochsToStartReceivingRewards, providertypes.DefaultNumberOfEpochsToStartReceivingRewards)
}

func MigrateMinPowerInTopN(ctx sdk.Context, providerKeeper providerkeeper.Keeper) {
	// we only get the registered consumer chains and not also the proposed consumer chains because
	// the minimal power is first set when the consumer chain addition proposal passes
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
			bondedValidators, err := providerKeeper.GetLastBondedValidators(ctx)
			if err != nil {
				providerKeeper.Logger(ctx).Error("failed to get last bonded validators", "chain", chain, "error", err)
				continue
			}
			minPower, err := providerKeeper.ComputeMinPowerInTopN(ctx, bondedValidators, topN)
			if err != nil {
				providerKeeper.Logger(ctx).Error("failed to compute min power in top N", "chain", chain, "topN", topN, "error", err)
				continue
			}
			providerKeeper.SetMinimumPowerInTopN(ctx, chain, minPower)
		}
	}
}
