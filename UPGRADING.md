# Upgrading Replicated Security

This guide provides instructions for upgrading to specific versions of Replicated Security.

## [v4.3.x](https://github.com/cosmos/interchain-security/releases/tag/v4.3.0)

### Provider

Upgrading a provider from `v4.2.0` to `v4.3.0` requires state migrations that will be done automatically via the upgrade module. 

### Consumer

***Note that consumer chains should not use this version of ICS***

## [v4.2.x](https://github.com/cosmos/interchain-security/releases/tag/v4.2.0)

### Provider

Upgrading a provider from `v4.1.0` or `v4.1.0-lsm` to `v4.2.0` or `v4.2.0-lsm` requires state migrations, see relevant pull request [here](https://github.com/cosmos/interchain-security/pull/1809)
for the corresponding migrators.

### Consumer

***Note that consumer chains should not use this version of ICS***

## [v4.1.x](https://github.com/cosmos/interchain-security/releases/tag/v4.1.0-rc2) and [v4.1.x-lsm](https://github.com/cosmos/interchain-security/releases/tag/v4.1.0-lsm-rc2)

### Provider

Upgrading a provider from `v4.0.0` to `v4.1.0` or `v4.1.0-lsm` requires state migrations, see relevant pull request [here](https://github.com/cosmos/interchain-security/pull/1762),
as well as the corresponding migrators [here](https://github.com/cosmos/interchain-security/blob/release/v4.1.x/x/ccv/provider/migrations/migrator.go#L38) and [here](https://github.com/cosmos/interchain-security/blob/release/v4.1.x-lsm/x/ccv/provider/migrations/migrator.go#L38).
Apart from running the ICS migrators, the provider chain also needs to initialize the `ConsumerValSet` for all existing consumer chains to ensure correct validator set replication.
To do so, the following code should be added to the upgrade handler of the provider chain:
```go
func InitICSEpochs(ctx sdk.Context, pk providerkeeper.Keeper, sk stakingkeeper.Keeper) error {
	ctx.Logger().Info("Initializing ICS epochs...")

	// get the bonded validators from the staking module
	bondedValidators := sk.GetLastValidators(ctx)

	for _, chain := range pk.GetAllConsumerChains(ctx) {
		chainID := chain.ChainId
		valset := pk.GetConsumerValSet(ctx, chainID)
		if len(valset) > 0 {
			ctx.Logger().Info("consumer chain `%s` already has the valset initialized", chainID)
		} else {
			// init valset for consumer with chainID
			nextValidators := pk.ComputeNextEpochConsumerValSet(ctx, chainID, bondedValidators)
			pk.SetConsumerValSet(ctx, chainID, nextValidators)
		}
	}

	ctx.Logger().Info("Finished initializing ICS epochs")
	return nil
}
```

### Consumer

***Note that consumer chains can upgrade directly from `v4.0.0` to `v4.1.0`.***

## [v4.0.x](https://github.com/cosmos/interchain-security/tree/release/v4.0.x)

`v4.0.x` sets the minimum required version of Go to `1.21`, see https://github.com/cosmos/interchain-security/blob/release/v4.0.x/go.mod#L3. 

### Provider 

Upgrading a provider from `v3.3.0` to `v4.0.0` will require state migrations, see https://github.com/cosmos/interchain-security/blob/release/v4.0.x/x/ccv/provider/migrations/migrator.go#L31. 

### Consumer 

***Note that consumer chains can upgrade directly from `v3.1.0` to `v4.0.0`.*** 

Upgrading a consumer from `v3.2.0` to `v4.0.0` will not require state migration, however, upgrading directly from `v3.1.0` to `v4.0.0` will require state migrations, see https://github.com/cosmos/interchain-security/blob/release/v4.0.x/x/ccv/consumer/keeper/migrations.go#L22. 

In addition, the following migration needs to be added to the upgrade handler of the consumer chain:
```golang
func migrateICSOutstandingDowntime(ctx sdk.Context, keepers *upgrades.UpgradeKeepers) error {
	ctx.Logger().Info("Migrating ICS outstanding downtime...")

	downtimes := keepers.ConsumerKeeper.GetAllOutstandingDowntimes(ctx)
	for _, od := range downtimes {
		consAddr, err := sdk.ConsAddressFromBech32(od.ValidatorConsensusAddress)
		if err != nil {
			return err
		}
		keepers.ConsumerKeeper.DeleteOutstandingDowntime(ctx, consAddr)
	}

	ctx.Logger().Info("Finished ICS outstanding downtime")

	return nil
}
```

## [v3.3.x](https://github.com/cosmos/interchain-security/tree/release/v3.2.x)

### Provider 

Upgrading the provider from `v2.x.y` to `v3.3.0` will not require state migration. 

## [v3.2.x](https://github.com/cosmos/interchain-security/tree/release/v3.2.x)

`v3.2.0` bumps IBC to `v7.3`. As a result, `legacy_ibc_testing` is not longer required and was removed, see https://github.com/cosmos/interchain-security/pull/1185. This means that when upgrading to `v3.2.0`, any customized tests relying on `legacy_ibc_testing` need to be updated.

### Consumer 

Upgrading the consumer from either `v3.0.0` or `v3.1.0` to `v3.2.0` will require state migrations, see https://github.com/cosmos/interchain-security/blob/release/v3.2.x/x/ccv/consumer/keeper/migration.go#L25.

## [v3.0.x](https://github.com/cosmos/interchain-security/releases/tag/v3.0.0-rc0)

### Upgrading to Cosmos SDK 0.47

The following should be considered as complementary to [Cosmos SDK v0.47 UPGRADING.md](https://github.com/cosmos/cosmos-sdk/blob/v0.47.0-rc2/UPGRADING.md).

#### Protobuf 

Protobuf code generation, linting and formatting have been updated to leverage the `ghcr.io/cosmos/proto-builder:0.11.5` docker container. Replicated Security protobuf definitions are now packaged and published to [buf.build/cosmos/interchain-security](https://buf.build/cosmos/interchain-security) via CI workflows. The `third_party/proto` directory has been removed in favour of dependency management using [buf.build](https://docs.buf.build/introduction).

#### App modules

Legacy APIs of the `AppModule` interface have been removed from ccv modules. For example, for 

```diff
- // Route implements the AppModule interface
- func (am AppModule) Route() sdk.Route {
-     return sdk.Route{}
- }
-
- // QuerierRoute implements the AppModule interface
- func (AppModule) QuerierRoute() string {
-     return types.QuerierRoute
- }
-
- // LegacyQuerierHandler implements the AppModule interface
- func (am AppModule) LegacyQuerierHandler(*codec.LegacyAmino) sdk.Querier {
-     return nil
- }
-
- // ProposalContents doesn't return any content functions for governance proposals.
- func (AppModule) ProposalContents(_ module.SimulationState) []simtypes.WeightedProposalContent {
-     return nil
- }
```

#### Imports

Imports for ics23 have been updated as the repository have been migrated from confio to cosmos.

```diff
import (
    // ...
-   ics23 "github.com/confio/ics23/go"
+   ics23 "github.com/cosmos/ics23/go"
    // ...
)
```

Imports for gogoproto have been updated.

```diff
import (
    // ...
-   "github.com/gogo/protobuf/proto"
+   "github.com/cosmos/gogoproto/proto"
    // ...
)
```

## [v2.0.x](https://github.com/cosmos/interchain-security/releases/tag/v2.0.0)

### Provider 

Upgrading a provider from `v1.1.0-multiden` to `v2.0.0` will require state migrations. See [migration.go](https://github.com/cosmos/interchain-security/blob/v2.0.0/x/ccv/provider/keeper/migration.go).

### Consumer

Upgrading a consumer from `v1.2.0-multiden` to `v2.0.0` will NOT require state migrations. 
