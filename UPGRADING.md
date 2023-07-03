# Upgrading Replicated Security

This guide provides instructions for upgrading to specific versions of Replicated Security.

## [v3.0.x](https://github.com/cosmos/interchain-security/releases/tag/v3.0.0-rc0)

### Upgrading to Cosmos SDK 0.47

The following should be considered as complementary to [Cosmos SDK v0.47 UPGRADING.md](https://github.com/cosmos/cosmos-sdk/blob/v0.47.0-rc2/UPGRADING.md).

#### Protobuf 

Protobuf code generation, linting and formatting have been updated to leverage the `ghcr.io/cosmos/proto-builder:0.11.5` docker container. Replicated Security protobuf definitions are now packaged and published to [buf.build/cosmos/interchain-security](buf.build/cosmos/interchain-security) via CI workflows. The `third_party/proto` directory has been removed in favour of dependency management using [buf.build](https://docs.buf.build/introduction).

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

Upgrading a provider from `v1.1.0-multiden` to `v2.0.0` will require state migrations. See [migration.go](./x/ccv/provider/keeper/migration.go). See the provider module's `ConsensusVersion` in [module](./x/ccv/provider/module.go).

### Consumer

Upgrading a consumer from `v1.2.0-multiden` to `v2.0.0` will NOT require state migrations. See the consumer module's `ConsensusVersion` in [module](./x/ccv/consumer/module.go).