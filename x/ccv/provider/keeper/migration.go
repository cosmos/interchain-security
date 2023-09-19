package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"
)

// Migrator is a struct for handling in-place store migrations.
type Migrator struct {
	providerKeeper Keeper
	paramSpace     paramtypes.Subspace
}

// NewMigrator returns a new Migrator.
func NewMigrator(providerKeeper Keeper, paramSpace paramtypes.Subspace) Migrator {
	return Migrator{providerKeeper: providerKeeper, paramSpace: paramSpace}
}

// Migrate2to3 migrates x/ccvprovider state from consensus version 2 to 3.
func (m Migrator) Migrate2to3(ctx sdk.Context) error {
	return m.providerKeeper.MigrateQueuedPackets(ctx)
}

func (k Keeper) MigrateQueuedPackets(ctx sdk.Context) error {
	return nil
}

// Pending packet data type enum, used to encode the type of packet data stored at each entry in the mutual queue.
const (
	slashPacketData byte = iota
	vscMaturedPacketData
)
