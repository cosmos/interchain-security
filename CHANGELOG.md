# CHANGELOG

## v3.3.0

*December 5, 2023*

### API BREAKING

- [Provider](x/ccv/provider)
  - Deprecate equivocation proposals.
    ([\#1340](https://github.com/cosmos/interchain-security/pull/1340))

### DEPENDENCIES

- Bump [ibc-go](https://github.com/cosmos/ibc-go) to
  [v7.3.1](https://github.com/cosmos/ibc-go/releases/tag/v7.3.1).
  ([\#1373](https://github.com/cosmos/interchain-security/pull/1373))

### FEATURES

- General
  - Add Quint model of Replicated Security.
    ([\#1336](https://github.com/cosmos/interchain-security/pull/1336))
- [Provider](x/ccv/provider)
  - Update how consumer-assigned keys are checked when a validator is
    created on the provider.
    ([\#1339](https://github.com/cosmos/interchain-security/pull/1339))
  - Introduce the cryptographic verification of equivocation feature to the provider
    (cf. [ADR-005](/docs/docs/adrs/adr-005-cryptographic-equivocation-verification.md)
    & [ADR-013](/docs/docs/adrs/adr-013-equivocation-slashing.md)).
    ([\#1340](https://github.com/cosmos/interchain-security/pull/1340))

### IMPROVEMENTS

- Split out consumer genesis state to reduce shared data between provider and
  consumer. ([\#1324](https://github.com/cosmos/interchain-security/pull/1324))
  - Note: This breaks json format used by augmenting Genesis files of consumer 
  chains with consumer genesis content exported from provider chain. Consumer 
  Genesis content exported from a provider chain using major version 1, 2 or 3 
  of the provider module needs to be transformed with the transformation command 
  introduced by this PR:
    ```
    Transform the consumer genesis file from a provider version v1, v2 or v3 to a version supported by this consumer. Result is printed to STDOUT.

    Example:
    $ <appd> transform /path/to/ccv_consumer_genesis.json

    Usage:
      interchain-security-cd genesis transform [genesis-file] [flags]
    ```
- Refactor shared events, codecs and errors assign to
  consumer and provider dedicated types where possible.
  ([\#1350](https://github.com/cosmos/interchain-security/pull/1350))

### STATE BREAKING

- General
  - Split out consumer genesis state to reduce shared data between provider and
    consumer. ([\#1324](https://github.com/cosmos/interchain-security/pull/1324))
  - Improve validation of IBC packet data and provider messages. Also,
    enable the provider to validate consumer packets before handling them.
    ([\#1460](https://github.com/cosmos/interchain-security/pull/1460))
- [Provider](x/ccv/provider)
  - Change the states by adding a consumer key for each chain that is
    not yet registered meaning for which the gov proposal has not passed.
    ([\#1339](https://github.com/cosmos/interchain-security/pull/1339))
  - Introduce the cryptographic verification of equivocation feature to the provider
    (cf. [ADR-005](/docs/docs/adrs/adr-005-cryptographic-equivocation-verification.md)
    & [ADR-013](/docs/docs/adrs/adr-013-equivocation-slashing.md)).
    ([\#1340](https://github.com/cosmos/interchain-security/pull/1340))

## v3.2.0

*November 24, 2023*

### BUG FIXES

- [Consumer](x/ccv/consumer)
  - Fix deletion of pending packets that may cause duplicate sends
    ([\#1146](https://github.com/cosmos/interchain-security/pull/1146))
  - Remove `idx` field from the `ccv.ConsumerPacketData` type as this would break the
    wire ([\#1150](https://github.com/cosmos/interchain-security/pull/1150))
  - Validate token transfer messages before calling `Transfer()`.
    ([\#1244](https://github.com/cosmos/interchain-security/pull/1244))
  - Remove incorrect address validation on `ProviderFeePoolAddrStr` param.
    ([\#1262](https://github.com/cosmos/interchain-security/pull/1262))
  - Increment consumer consensus version and register consumer migration.
    ([\#1295](https://github.com/cosmos/interchain-security/pull/1295))

### DEPENDENCIES

- Bump [ibc-go](https://github.com/cosmos/ibc-go) to
  [v7.2.0](https://github.com/cosmos/ibc-go/releases/tag/v7.2.0).
  ([\#1196](https://github.com/cosmos/interchain-security/pull/1196))
- Bump [cosmos-sdk](https://github.com/cosmos/cosmos-sdk) to
  [v0.47.4](https://github.com/cosmos/cosmos-sdk/releases/tag/v0.47.4).
  ([\#1258](https://github.com/cosmos/interchain-security/pull/1258))
- Bump [ibc-go](https://github.com/cosmos/ibc-go) to
  [v7.3.0](https://github.com/cosmos/ibc-go/releases/tag/v7.3.0).
  ([\#1258](https://github.com/cosmos/interchain-security/pull/1258))
- Bump [cosmos-sdk](https://github.com/cosmos/cosmos-sdk) to
  [v0.47.5](https://github.com/cosmos/cosmos-sdk/releases/tag/v0.47.5).
  ([\#1259](https://github.com/cosmos/interchain-security/pull/1259))

### FEATURES

- [Consumer](x/ccv/consumer)
  - Add the consumer-side changes for jail throttling with retries (cf. ADR 008).
    ([\#1024](https://github.com/cosmos/interchain-security/pull/1024))
  - Introduce the gRPC query `/interchain_security/ccv/consumer/provider-
    info` and CLI command `interchain-security-cd q ccvconsumer
    provider-info` to retrieve provider info from the consumer chain.
    ([\#1164](https://github.com/cosmos/interchain-security/pull/1164))
- [Provider](x/ccv/provider)
  - Add `InitTimeoutTimestamps` and `ExportedVscSendTimestamps` to exported
    genesis. ([\#1076](https://github.com/cosmos/interchain-security/pull/1076))
  - Add a governance proposal for setting on the provider the denominations for
    rewards from consumer chains.
    ([\#1280](https://github.com/cosmos/interchain-security/pull/1280))

### IMPROVEMENTS

- General
  - Update the default consumer unbonding period to 2 weeks.
    ([\#1244](https://github.com/cosmos/interchain-security/pull/1244))
- [Consumer](x/ccv/consumer)
  - Optimize pending packets storage on consumer, with migration.
    ([\#1037](https://github.com/cosmos/interchain-security/pull/1037))

### STATE BREAKING

- General
  - Bump [ibc-go](https://github.com/cosmos/ibc-go) to
    [v7.2.0](https://github.com/cosmos/ibc-go/releases/tag/v7.2.0).
    ([\#1196](https://github.com/cosmos/interchain-security/pull/1196))
  - Update the default consumer unbonding period to 2 weeks.
    ([\#1244](https://github.com/cosmos/interchain-security/pull/1244))
  - Bump [cosmos-sdk](https://github.com/cosmos/cosmos-sdk) to
    [v0.47.4](https://github.com/cosmos/cosmos-sdk/releases/tag/v0.47.4).
    ([\#1258](https://github.com/cosmos/interchain-security/pull/1258))
  - Bump [ibc-go](https://github.com/cosmos/ibc-go) to
    [v7.3.0](https://github.com/cosmos/ibc-go/releases/tag/v7.3.0).
    ([\#1258](https://github.com/cosmos/interchain-security/pull/1258))
  - Bump [cosmos-sdk](https://github.com/cosmos/cosmos-sdk) to
    [v0.47.5](https://github.com/cosmos/cosmos-sdk/releases/tag/v0.47.5).
    ([\#1259](https://github.com/cosmos/interchain-security/pull/1259))
- [Consumer](x/ccv/consumer)
  - Add the consumer-side changes for jail throttling with retries (cf. ADR 008).
    ([\#1024](https://github.com/cosmos/interchain-security/pull/1024))
  - Optimize pending packets storage on consumer, with migration.
    ([\#1037](https://github.com/cosmos/interchain-security/pull/1037))
  - Fix deletion of pending packets that may cause duplicate sends
    ([\#1146](https://github.com/cosmos/interchain-security/pull/1146))
  - Remove `idx` field from the `ccv.ConsumerPacketData` type as this would break the
    wire ([\#1150](https://github.com/cosmos/interchain-security/pull/1150))
  - Validate token transfer messages before calling `Transfer()`.
    ([\#1244](https://github.com/cosmos/interchain-security/pull/1244))
  - Remove incorrect address validation on `ProviderFeePoolAddrStr` param.
    ([\#1262](https://github.com/cosmos/interchain-security/pull/1262))
  - Increment consumer consensus version and register consumer migration.
    ([\#1295](https://github.com/cosmos/interchain-security/pull/1295))
- [Provider](x/ccv/provider)
  - Add a governance proposal for setting on the provider the denominations for
    rewards from consumer chains.
    ([\#1280](https://github.com/cosmos/interchain-security/pull/1280))

## v3.1.0

Date July 11th, 2023

A minor upgrade to v3.0.0, which removes the panic in the consumer ccv module which would occur in an emergency scenario where the ccv channel is closed. This release also fixes how a distribution related event is emitted, and bumps cometbft.

* (feat) [#1127](https://github.com/cosmos/interchain-security/pull/1127) Remove consumer panic when ccv channel is closed
* (fix) [#720](https://github.com/cosmos/interchain-security/issues/720) Fix the attribute `AttributeDistributionTotal` value in `FeeDistribution` event emit.
* (deps) [#1119](https://github.com/cosmos/interchain-security/pull/1119) bump cometbft from `v0.37.1` to `0.37.2`.

## v3.0.0

Date: June 21st, 2023

Interchain Security v3 uses SDK 0.47 and IBC 7.

* (fix) [#1093](https://github.com/cosmos/interchain-security/pull/1093) Make SlashPacketData backward compatible when sending data over the wire 
* (deps) [#1019](https://github.com/cosmos/interchain-security/pull/1019) Bump multiple dependencies. 
  * Bump [cosmos-sdk](https://github.com/cosmos/cosmos-sdk) to [v0.47.3](https://github.com/cosmos/cosmos-sdk/releases/tag/v0.47.3).
  * Bump [ibc-go](https://github.com/cosmos/ibc-go) to [v7.1.0](https://github.com/cosmos/ibc-go/releases/tag/v7.1.0).
  * Bump [CometBFT](https://github.com/cometbft/cometbft) to [v0.37.1](https://github.com/cometbft/cometbft/releases/tag/v0.37.1).
* `[x/ccv/provider]` (fix) [#945](https://github.com/cosmos/interchain-security/issues/945) Refactor `AfterUnbondingInitiated` to not panic when `PutUnbondingOnHold` returns error.
* `[x/ccv/provider]` (fix) [#977](https://github.com/cosmos/interchain-security/pull/977) Avoids panicking the provider when an unbonding delegation was removed through a `CancelUnbondingDelegation` message.
* `[x/ccv/democracy]` (feat) [#1019](https://github.com/cosmos/interchain-security/pull/1019) Whitelisting non-legacy params in the "democracy module" require the entire module to be whitelisted. 

## Previous Versions

[CHANGELOG of previous versions](https://github.com/cosmos/interchain-security/blob/main/CHANGELOG.md)

