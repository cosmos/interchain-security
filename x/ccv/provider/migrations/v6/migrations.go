package v6

import (
	sdk "github.com/cosmos/cosmos-sdk/types"

	providerkeeper "github.com/cosmos/interchain-security/v5/x/ccv/provider/keeper"
	ccvtypes "github.com/cosmos/interchain-security/v5/x/ccv/types"
)

// MigrateParams migrates the provider module's parameters from the x/params to self store.
func MigrateLegacyParams(ctx sdk.Context, keeper providerkeeper.Keeper, legacyParamspace ccvtypes.LegacyParamSubspace) error {
	ctx.Logger().Info("starting provider legacy params migration")
	params := GetParamsLegacy(ctx, legacyParamspace)
	err := params.Validate()
	if err != nil {
		return err
	}

	keeper.SetParams(ctx, params)
	keeper.Logger(ctx).Info("successfully migrated legacy provider parameters")
	return nil
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
