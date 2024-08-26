package migrations

import (
	"fmt"

	storetypes "cosmossdk.io/store/types"
	sdktypes "github.com/cosmos/cosmos-sdk/types"
	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"

	providerkeeper "github.com/cosmos/interchain-security/v5/x/ccv/provider/keeper"
	v4 "github.com/cosmos/interchain-security/v5/x/ccv/provider/migrations/v4"
	v5 "github.com/cosmos/interchain-security/v5/x/ccv/provider/migrations/v5"
	v6 "github.com/cosmos/interchain-security/v5/x/ccv/provider/migrations/v6"
	v7 "github.com/cosmos/interchain-security/v5/x/ccv/provider/migrations/v7"
	v8 "github.com/cosmos/interchain-security/v5/x/ccv/provider/migrations/v8"
)

// Migrator is a struct for handling in-place store migrations.
type Migrator struct {
	providerKeeper providerkeeper.Keeper
	paramSpace     paramtypes.Subspace
	storeKey       storetypes.StoreKey
}

// NewMigrator returns a new Migrator.
func NewMigrator(
	providerKeeper providerkeeper.Keeper,
	paramSpace paramtypes.Subspace,
	storeKey storetypes.StoreKey,
) Migrator {
	return Migrator{
		providerKeeper: providerKeeper,
		paramSpace:     paramSpace,
		storeKey:       storeKey,
	}
}

// Migrating consensus version 1 to 2 is a no-op.
// Migrating from v1 -> v2 -> v3 will require multiple state breaking changes and migrations.
// First run provider@v2.x.y in production to migrate from consensus version 1 to 2.
// Then, in order to migrate to consensus version 3, first upgrade to provider@v3.x.y.
func (m Migrator) Migrate1to2(ctx sdktypes.Context) error {
	return fmt.Errorf("state migration failed: " +
		"first run provider@v2.x.y in production to migrate from consensus version 1 to 2; " +
		"then, in order to migrate to consensus version 3, first upgrade to provider@v3.x.y")
}

// Migrate2to3 migrates x/ccvprovider state from consensus version 2 to 3.
// First run provider@v4.0.x in production to migrate from consensus version 2 to 3.
func (m Migrator) Migrate2to3(ctx sdktypes.Context) error {
	return fmt.Errorf("state migration failed: " +
		"first run provider@v4.0.x in production to migrate from consensus version 2 to 3")
}

// Migrate3to4 migrates x/ccvprovider state from consensus version 3 to 4.
// The migration consists of provider chain params additions.
func (m Migrator) Migrate3to4(ctx sdktypes.Context) error {
	v4.MigrateParams(ctx, m.paramSpace)
	return nil
}

// Migrate4to5 migrates x/ccvprovider state from consensus version 4 to 5.
// The migration consists of setting a top N of 95 for all registered consumer chains.
func (m Migrator) Migrate4to5(ctx sdktypes.Context) error {
	v5.MigrateTopNForRegisteredChains(ctx, m.providerKeeper)
	return nil
}

// Migrate5to6 migrates x/ccvprovider state from consensus version 5 to 6.
// It consists of setting the `NumberOfEpochsToStartReceivingRewards` param, as well as
// computing and storing the minimal power in the top N for all registered consumer chains.
func (m Migrator) Migrate5to6(ctx sdktypes.Context) error {
	v6.MigrateParams(ctx, m.paramSpace)
	v6.MigrateMinPowerInTopN(ctx, m.providerKeeper)
	return nil
}

// Migrate6to7 migrates x/ccvprovider state from consensus version 6 to 7.
// The migration consists of initializing new provider chain params using params from the legacy store.
func (m Migrator) Migrate6to7(ctx sdktypes.Context) error {
	return v7.MigrateLegacyParams(ctx, m.providerKeeper, m.paramSpace)
}

// Migrate7to8 migrates x/ccvprovider state from consensus version 7 to 8.
// The migration consists of the following actions:
// - complete the outstanding paused unbonding ops waiting for VSCMaturedPackets from consumer chains
// - migrate the ConsumerAddrsToPrune index to ConsumerAddrsToPruneV2
// - cleanup deprecated state
func (m Migrator) Migrate7to8(ctx sdktypes.Context) error {
	store := ctx.KVStore(m.storeKey)
	v8.CompleteUnbondingOps(ctx, store, m.providerKeeper)
	if err := v8.MigrateConsumerAddrsToPrune(ctx, store, m.providerKeeper); err != nil {
		return err
	}
	if err := v8.MigrateLaunchedConsumerChains(ctx, store, m.providerKeeper); err != nil {
		return err
	}
	if err := v8.MigratePreLaunchedConsumerChains(ctx, store, m.providerKeeper); err != nil {
		return err
	}
	if err := v8.MigrateStoppedConsumerChains(ctx, store, m.providerKeeper); err != nil {
		return err
	}
	v8.CleanupState(store)

	return nil
}
