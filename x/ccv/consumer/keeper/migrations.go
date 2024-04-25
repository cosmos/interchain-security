package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"

	v2 "github.com/cosmos/interchain-security/v5/x/ccv/consumer/migrations/v2"
	v3 "github.com/cosmos/interchain-security/v5/x/ccv/consumer/migrations/v3"
)

// Migrator is a struct for handling in-place store migrations.
type Migrator struct {
	keeper     Keeper
	paramSpace paramtypes.Subspace
}

// NewMigrator returns a new Migrator.
func NewMigrator(keeper Keeper, paramspace paramtypes.Subspace) Migrator {
	return Migrator{keeper: keeper, paramSpace: paramspace}
}

// Migrate1to2 migrates x/ccvconsumer state from consensus version 1 to 2.
func (m Migrator) Migrate1to2(ctx sdk.Context) error {
	store := ctx.KVStore(m.keeper.storeKey)
	return v2.MigrateConsumerPacketData(ctx, store)
}

// Migrate2to3 migrates x/ccvconsumer from consensus version 2 to 3.
// This migration is necessary to move the consumer module legacy params.
func (m Migrator) Migrate2to3(ctx sdk.Context) error {
	store := ctx.KVStore(m.keeper.storeKey)
	cdc := m.keeper.cdc
	return v3.MigrateLegacyParams(ctx, cdc, store, m.paramSpace)
}
