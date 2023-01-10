# Legacy IBC Testing

### `legacy_ibc_testing` is imported from [Informal Systems fork of ibc-go](https://github.com/informalsystems/ibc-go). It contains modifications to canonical ibc-go `v3.4.0` for testing purposes only.

Crucially, Informal's fork contained changes to the [StakingKeeper interface](https://github.com/informalsystems/ibc-go/blob/interchain-security-v3.4.0/modules/core/02-client/types/expected_keepers.go#L12) that both consumer and providers would be expected to return from the testing method `GetStakingKeeper`. For consumer apps, this method would return and IBCKeeper type. This change could not be back-ported to `v3.4.0` of ibc-go as it would be api breaking. Instead, the relevant changes made to ibc-go were consolidated and copied directly into `interchain-security`. Once ICS upgrades ibc-go to a version that supports this change, `v5` at the earliest, this test helper directory can be removed.

**Directory**
- Core
  - Contains changes made in ibc-go `core/`, but do not contain any logic requiring they live in that directory. Includes an interface definition and a testing helper method.
- Simapp
  - Includes test helper substitutions for ibc-go's `simapp/` used in the Diff tests. 
- Testing
  - Replaces ibc-go's `testing/` directory to facilitate ibc's `TestApp`'s implementation of `GetStakingKeeper` returning the relevant `StakingKeeper` interface enhanced in Informal's ibc-go fork.