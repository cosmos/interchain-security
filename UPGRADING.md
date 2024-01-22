# Upgrading Replicated Security

This guide provides instructions for upgrading to specific versions of Replicated Security.

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