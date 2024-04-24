package v5

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
