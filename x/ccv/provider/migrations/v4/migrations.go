package v4

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"

	providerkeeper "github.com/cosmos/interchain-security/v5/x/ccv/provider/keeper"
)

// MigrateParams migrates the provider module's parameters from the x/params to self store.
func MigrateParams(ctx sdk.Context, keeper providerkeeper.Keeper, legacySubspace paramtypes.Subspace) error {
	keeper.Logger(ctx).Info("starting provider params migration")
	params := providerkeeper.GetParamsLegacy(ctx, legacySubspace)
	err := params.Validate()
	if err != nil {
		return err
	}

	keeper.SetParams(ctx, params)
	keeper.Logger(ctx).Info("successfully migrated provider parameters")
	return nil
}
