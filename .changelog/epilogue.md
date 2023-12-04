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
