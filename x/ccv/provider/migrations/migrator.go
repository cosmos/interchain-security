package migrations

import (
	sdktypes "github.com/cosmos/cosmos-sdk/types"
	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"

	providerkeeper "github.com/cosmos/interchain-security/v3/x/ccv/provider/keeper"
	v3 "github.com/cosmos/interchain-security/v3/x/ccv/provider/migrations/v3"
)

// Migrator is a struct for handling in-place store migrations.
type Migrator struct {
	providerKeeper providerkeeper.Keeper
	paramSpace     paramtypes.Subspace
}

// NewMigrator returns a new Migrator.
func NewMigrator(providerKeeper providerkeeper.Keeper, paramSpace paramtypes.Subspace) Migrator {
	return Migrator{providerKeeper: providerKeeper, paramSpace: paramSpace}
}

// Migrating consensus version 1 to 2 is a no-op.
// <igrating from v1 -> v2 -> v3  will require multiple state breaking changes and migrations.
// First run provider@v2.x.y in production to migrate from v1 -> v2. Then use provider@v3.x.y to migrate from v2 -> v3.
func (m Migrator) Migrate1to2(ctx sdktypes.Context) error {
	return nil
}

// Migrate2to3 migrates x/ccvprovider state from consensus version 2 to 3.
func (m Migrator) Migrate2to3(ctx sdktypes.Context) error {
	return v3.MigrateQueuedPackets(ctx, m.providerKeeper)
}
