<!--
  A release notes template that should be adapted for every release
    - release: v6.0.0
    - release branch: v6.0.x
    - the last release: v5.2.0
    - the last release branch: v5.2.x
-->

# Interchain Security v6.0.0  Release Notes

❗ ***Note this release is ONLY relevant to providers***

## 📝 Changelog

Check out the [changelog](https://github.com/cosmos/interchain-security/blob/v6.0.0/CHANGELOG.md) for a list of relevant changes or [compare all changes](https://github.com/cosmos/interchain-security/compare/<v-last>...v6.0.0) from last release.

Refer to the [upgrading guide](https://github.com/cosmos/interchain-security/blob/release/v6.0.x/UPGRADING.md) when migrating from `v5.2.x` to `v6.0.x`.

## 🚀 Highlights

<!-- Add any highlights of this release -->

This release introduces the following features:

- Permissionless (as described in [ADR 019](https://cosmos.github.io/interchain-security/adrs/adr-019-permissionless-ics)) enables users to permissionlessly launch opt-in consumer chains. Note that Top N consumer chains will still need to go through governance. 
- Inactive Provider Validators (as described in [ADR 017](https://cosmos.github.io/interchain-security/adrs/adr-017-allowing-inactive-validators)) enables validators from outside the provider's active validator set to validate on consumer chains.
- Removal of Unbonding Pausing (i.e., the provider-side changes of [ADR 018](https://cosmos.github.io/interchain-security/adrs/adr-018-remove-vscmatured)) reduces the complexity of the ICS protocol and removes the dependency between the liveness of undelegation operations on the Cosmos Hub and the liveness of consumer chains.

In addition, it bumps the following dependencies:

- CometBFT to [v0.38.11](https://github.com/cometbft/cometbft/releases/tag/v0.38.11)
- Cosmos SDK to [v0.50.9](https://github.com/cosmos/cosmos-sdk/releases/tag/v0.50.9)
- IBC-Go to [v8.5.0](https://github.com/cosmos/ibc-go/releases/tag/v8.5.0)
