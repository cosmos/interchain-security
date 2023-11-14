package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"
)

type Migrator struct {
	keeper         Keeper
	legacySubspace paramtypes.Subspace
}

// NewMigrator returns a new Migrator.
func NewMigrator(keeper Keeper, subspace paramtypes.Subspace) Migrator {
	return Migrator{
		keeper:         keeper,
		legacySubspace: subspace,
	}
}

// MigrateParams migrates the provider module's parameters from the x/params to self store.
func (m Migrator) MigrateParams(ctx sdk.Context) error {
	params := GetParamsLegacy(ctx, m.legacySubspace)
	err := params.Validate()
	if err != nil {
		return err
	}
	m.keeper.SetParams(ctx, params)
	m.keeper.Logger(ctx).Info("successfully migrated provider parameters")
	return nil
}
