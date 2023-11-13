package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"
	"github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
)

type Migrator struct {
	keeper Keeper
}

// NewMigrator returns a new Migrator.
func NewMigrator(keeper Keeper) Migrator {
	return Migrator{
		keeper: keeper,
	}
}

// MigrateParams migrates the provider module's parameters from the x/params to self store.
func (m Migrator) MigrateParams(ctx sdk.Context, paramSpace paramtypes.Subspace) error {
	var params types.Params
	paramSpace.GetParamSet(ctx, &params)

	m.keeper.SetParams(ctx, params)
	m.keeper.Logger(ctx).Info("successfully migrated provider parameters")
	return nil
}
