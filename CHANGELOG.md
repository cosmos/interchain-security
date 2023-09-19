# CHANGELOG

## [Unreleased for Provider]

Add an entry to the unreleased provider section whenever merging a PR to main that is not targeted at a specific release. These entries will eventually be included in a provider release.

* (feature!) [#1244](https://github.com/cosmos/interchain-security/pull/1244) Update the default consumer unbonding period to 2 weeks.
* (deps) [#1259](https://github.com/cosmos/interchain-security/pull/1259) Bump [cosmos-sdk](https://github.com/cosmos/cosmos-sdk) to [v0.47.5](https://github.com/cosmos/cosmos-sdk/releases/tag/v0.47.5).
* (deps!) [#1258](https://github.com/cosmos/interchain-security/pull/1258) Bump [ibc-go](https://github.com/cosmos/ibc-go) to [v7.3.0](https://github.com/cosmos/ibc-go/releases/tag/v7.3.0).
* (deps) [#1258](https://github.com/cosmos/interchain-security/pull/1258) Bump [cosmos-sdk](https://github.com/cosmos/cosmos-sdk) to [v0.47.4](https://github.com/cosmos/cosmos-sdk/releases/tag/v0.47.4).
* (deps!) [#1196](https://github.com/cosmos/interchain-security/pull/1196) Bump [ibc-go](https://github.com/cosmos/ibc-go) to [v7.2.0](https://github.com/cosmos/ibc-go/releases/tag/v7.2.0).
* `[x/ccv/provider]` (fix) [#1076](https://github.com/cosmos/interchain-security/pull/1076) Add `InitTimeoutTimestamps` and `ExportedVscSendTimestamps` to exported genesis.

## [Unreleased for Consumer]

Add an entry to the unreleased consumer section whenever merging a PR to main that is not targeted at a specific release. These entries will eventually be included in a consumer release.

## v3.2.0-consumer

Date September 6th, 2023

A minor version upgrade to the CONSUMER CCV module. This release includes various changes involving throttling v2 functionality, validation, and bumps to deps like cosmos-sdk and ibc-go.

Note:

* This release is ONLY RELEVANT TO CONSUMERS. The most recent provider release is v3.1.0, and will eventually be a release postfixed with `-provider`.
* this is the first upgrade to the consumer module with a separate semver cycle from the provider module. See [contributing.md](./CONTRIBUTING.md#semantic-versioning) and [associated ADR](docs/docs/adrs/adr-012-separate-releasing.md) for more info.

Changes:

* (feat) [#1295](https://github.com/cosmos/interchain-security/pull/1295) increment consumer consensus version and register consumer packet migration.
* (fix!) [#1262](https://github.com/cosmos/interchain-security/pull/1262) Remove incorrect address validation on `ProviderFeePoolAddrStr` param.
* (feature!) [#1244](https://github.com/cosmos/interchain-security/pull/1244) Update the default consumer unbonding period to 2 weeks.
* (fix!) [#1244](https://github.com/cosmos/interchain-security/pull/1244) Validate token transfer messages before calling `Transfer()`.
* (deps) [#1259](https://github.com/cosmos/interchain-security/pull/1259) Bump [cosmos-sdk](https://github.com/cosmos/cosmos-sdk) to [v0.47.5](https://github.com/cosmos/cosmos-sdk/releases/tag/v0.47.5).
* (deps!) [#1258](https://github.com/cosmos/interchain-security/pull/1258) Bump [ibc-go](https://github.com/cosmos/ibc-go) to [v7.3.0](https://github.com/cosmos/ibc-go/releases/tag/v7.3.0).
* (deps) [#1258](https://github.com/cosmos/interchain-security/pull/1258) Bump [cosmos-sdk](https://github.com/cosmos/cosmos-sdk) to [v0.47.4](https://github.com/cosmos/cosmos-sdk/releases/tag/v0.47.4).
* (deps!) [#1196](https://github.com/cosmos/interchain-security/pull/1196) Bump [ibc-go](https://github.com/cosmos/ibc-go) to [v7.2.0](https://github.com/cosmos/ibc-go/releases/tag/v7.2.0).
* (feat!) [#1024](https://github.com/cosmos/interchain-security/pull/1024) Throttle with retries, consumer changes.  
* (fix!) [#1150](https://github.com/cosmos/interchain-security/pull/1150) Revert consumer packet data changes from #1037.
* (fix!) [#1146](https://github.com/cosmos/interchain-security/pull/1146) Proper deletion of pending packets.
* (feat!) [#1037](https://github.com/cosmos/interchain-security/pull/1037) Optimize pending packets storage on consumer, with migration.
* (feat) [#1164](https://github.com/cosmos/interchain-security/pull/1164) Introduce the gRPC query `/interchain_security/ccv/consumer/provider-info` and CLI command `interchain-security-cd q ccvconsumer provider-info` to retrieve provider info from the consumer chain.

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

## v2.0.0

Date: June 1st, 2023

Unlike prior releases, the ICS `v2.0.0` release will be based on the main branch. `v2.0.0` will contain all the accumulated PRs from the various releases below, along with other PRs that were merged, but not released to production. After `v2.0.0`, we plan to revamp release practices, and how we modularize the repo for consumer/provider.

Upgrading a provider from `v1.1.0-multiden` to `v2.0.0` will require state migrations. See [migration.go](./x/ccv/provider/keeper/migration.go). See the provider module's `ConsensusVersion` in [module](./x/ccv/provider/module.go)

Upgrading a consumer from `v1.2.0-multiden` to `v2.0.0` will NOT require state migrations. See the consumer module's `ConsensusVersion` in [module](./x/ccv/consumer/module.go)

Some PRs from v2.0.0 may reappear from other releases below. This is due to the fact that ICS v1.1.0 deviates from the commit ordering of the main branch, and other releases thereafter are based on v1.1.0.

### High level changes included in v2.0.0

* MVP for standalone to consumer changeover, see [EPIC](https://github.com/cosmos/interchain-security/issues/756)
* MVP for soft opt out, see [EPIC](https://github.com/cosmos/interchain-security/issues/851)
* Various fixes, critical and non-critical
* Docs updates which should not affect production code

## Notable PRs included in v2.0.0

* (feat!) Add DistributionTransmissionChannel to ConsumerAdditionProposal [#965](https://github.com/cosmos/interchain-security/pull/965)
* (feat/fix) limit vsc matured packets handled per endblocker [#1004](https://github.com/cosmos/interchain-security/pull/1004)
* (fix) cosumer key prefix order to avoid complex migrations [#963](https://github.com/cosmos/interchain-security/pull/963) and [#991](https://github.com/cosmos/interchain-security/pull/991). The latter PR is the proper fix.
* (feat) v1->v2 migrations to accommodate a bugfix having to do with store keys, introduce new params, and deal with consumer genesis state schema changes [#975](https://github.com/cosmos/interchain-security/pull/975) and [#997](https://github.com/cosmos/interchain-security/pull/997)
* (deps) Bump github.com/cosmos/ibc-go/v4 from 4.4.0 to 4.4.2 [#982](https://github.com/cosmos/interchain-security/pull/982)
* (fix) partially revert key assignment type safety PR [#980](https://github.com/cosmos/interchain-security/pull/980)
* (fix) Remove panics on failure to send IBC packets [#876](https://github.com/cosmos/interchain-security/pull/876)
* (fix) Prevent denom DOS [#931](https://github.com/cosmos/interchain-security/pull/931)
* (fix) multisig for assigning consumer key, use json [#916](https://github.com/cosmos/interchain-security/pull/916)
* (deps) Bump github.com/cosmos/ibc-go/v4 from 4.3.0 to 4.4.0 [#902](https://github.com/cosmos/interchain-security/pull/902)
* (feat) Add warnings when provider unbonding is shorter than consumer unbonding [#858](https://github.com/cosmos/interchain-security/pull/858)
* (chore) use go 1.19 [#899](https://github.com/cosmos/interchain-security/pull/899), [#840](https://github.com/cosmos/interchain-security/pull/840)
* (feat) Standalone to consumer changeover - recycle existing transfer channel [#832](https://github.com/cosmos/interchain-security/pull/832)
* (deps) Bump IBC [862](https://github.com/cosmos/interchain-security/pull/862)
* (testing) Add tests for soft opt out [#857](https://github.com/cosmos/interchain-security/pull/857)
* (feat) Standalone to consumer changeover - staking functionalities [#794](https://github.com/cosmos/interchain-security/pull/794)
* (fix) prevent provider from sending VSCPackets with multiple updates for the same validator [#850](https://github.com/cosmos/interchain-security/pull/850)
* (feat) Soft opt out [#833](https://github.com/cosmos/interchain-security/issues/833)
* (fix) Correctly handle VSC packet with duplicate val updates on consumer [#846](https://github.com/cosmos/interchain-security/pull/846)
* (deps) bump sdk to v0.45.15.ics [#805](https://github.com/cosmos/interchain-security/pull/805)
* (refactor) Remove spm module [#812](https://github.com/cosmos/interchain-security/pull/812)
* (feat) Standalone to consumer changeover part 1 [#757](https://github.com/cosmos/interchain-security/pull/757)
* (chore) Swap names of e2e and integration tests [#681](https://github.com/cosmos/interchain-security/pull/681)
* (fix) fix StopConsumerChain not running in cachedContext [#802](https://github.com/cosmos/interchain-security/pull/802). Also in earlier releases with different commit order!
* (docs) Introduce docs website [#759](https://github.com/cosmos/interchain-security/pull/759)
* (fix) Serialize correct byte prefix for SlashLogKey [#786](https://github.com/cosmos/interchain-security/pull/786)
* (feature) Improve keeper field validation [#766](https://github.com/cosmos/interchain-security/pull/766)
* (docs) Contributing guidelines [#744](https://github.com/cosmos/interchain-security/pull/744)
* (refactor) Key assignment type safety [#725](https://github.com/cosmos/interchain-security/pull/725) 
* (fix) Update protos and fix deps [#752](https://github.com/cosmos/interchain-security/pull/752)
* (api) Add consumer QueryParams [#746](https://github.com/cosmos/interchain-security/pull/746)
* (feature) New validation for keeper fields [#740](https://github.com/cosmos/interchain-security/pull/740)

## v1.2.0-multiden

The first release candidate for a fix built on top of v1.2.0, intended for consumers. This release adds a list of denoms on the consumer that are allowed to be sent to the provider as rewards. This prevents a potential DOS attack that was discovered during the audit of Replicated Security performed by Oak Security and funded by the Cosmos Hub community through Proposal 687. In an effort to move quickly, this release also includes a multisig fix that is effective only for provider. It shouldn't affect the consumer module.

Note PRs were made in a private security repo.

[full diff](https://github.com/cosmos/interchain-security/compare/v1.2.0...v1.2.0-multiden-rc0)

## v1.1.0-multiden

This release combines two fixes on top of v1.1.0, that we judged were urgent to get onto the Cosmos Hub before the launch of the first ICS consumer chain. This is an emergency release intended for providers.

The first fix is to enable the use of multisigs and Ledger devices when assigning keys for consumer chains. The second is to prevent a possible DOS vector involving the reward distribution system.

Note PRs were made in a private security repo.

[full diff](https://github.com/cosmos/interchain-security/compare/v1.1.0...release/v1.1.0-multiden)

### Multisig fix

On April 25th (a week and a half ago), we began receiving reports that validators using multisigs and Ledger devices were getting errors reading Error: unable to resolve type URL /interchain_security.ccv.provider.v1.MsgAssignConsumerKey: tx parse error when attempting to assign consensus keys for consumer chains.

We quickly narrowed the problem down to issues having to do with using the PubKey type directly in the MsgAssignConsumerKey transaction, and Amino (a deprecated serialization library still used in Ledger devices and multisigs) not being able to handle this. We attempted to fix this with the assistance of the Cosmos-SDK team, but after making no headway for a few days, we decided to simply use a JSON representation of the PubKey in the transaction. This is how it is usually represented anyway. We have verified that this fixes the problem.

### Distribution fix

The ICS distribution system works by allowing consumer chains to send rewards to a module address on the provider called the FeePoolAddress. From here they are automatically distributed to all validators and delegators through the distribution system that already exists to distribute staking rewards. The FeePoolAddress is usually blocked so that no tokens can be sent to it, but to enable ICS distribution we had to unblock it.

We recently realized that unblocking the FeePoolAddress could enable an attacker to send a huge number of different denoms into the distribution system. The distribution system would then attempt to distribute them all, leading to out of memory errors. Fixing a similar attack vector that existed in the distribution system before ICS led us to this realization.

To fix this problem, we have re-blocked the FeePoolAddress and created a new address called the ConsumerRewardsPool. Consumer chains now send rewards to this new address. There is also a new transaction type called RegisterConsumerRewardDenom. This transaction allows people to register denoms to be used as rewards from consumer chains. It costs 10 Atoms to run this transaction.The Atoms are transferred to the community pool. Only denoms registered with this command are then transferred to the FeePoolAddress and distributed out to delegators and validators.

## v1.2.1

* (fix) Remove SPM [#812](https://github.com/cosmos/interchain-security/pull/812)
* (refactor) Key assignment type safety [#725](https://github.com/cosmos/interchain-security/pull/725)

## v1.2.0

Date: April 13th, 2023

* (feat) Soft opt-out [#833](https://github.com/cosmos/interchain-security/pull/833)
* (fix) Correctly handle VSC packet with duplicate val updates on consumer [#846](https://github.com/cosmos/interchain-security/pull/846)
* (chore) bump: sdk v0.45.15-ics [#805](https://github.com/cosmos/interchain-security/pull/805)
* (api) add interchain security consumer QueryParams [#746](https://github.com/cosmos/interchain-security/pull/746)

## v1.1.1

* (fix) Remove SPM [#812](https://github.com/cosmos/interchain-security/pull/812)
* (refactor) Key assignment type safety [#725](https://github.com/cosmos/interchain-security/pull/725)

## v1.1.0

Date: March 24th, 2023

* (fix) StopConsumerChain not running in cachedContext [#802](https://github.com/cosmos/interchain-security/pull/802)

## v1.0.0

Date: February 6th, 2023

This is the first version of Interchain Security (ICS), also known as _Replicated Security_ (RS).
Replicated Security is a feature which will allow a chain -- referred to as the _provider_ -- to share security with other chains -- referred to as _consumers_.
This means that the provider's validator set will be granted the right to validate consumer chains.
The communication between the provider and the consumer chains is done through the IBC protocol over a unique, ordered channel (one for each consumer chain). Thus, RS is an IBC application.

### Features / sub-protocols

RS consist of the following core features:

- **Channel Initialization**: Enables the provider to add new consumer chains. This process is governance-gated, i.e., to add a new consumer chain, a `ConsumerAdditionProposal` governance proposal must be sent to the provider and it must receive the necessary votes.
- **Validator Set Update**: Enables the provider to 
  (1) update the consumers on the voting power granted to validators (based on the changes in the active validator set on the provider chain), 
  and (2) ensure the timely completion of unbonding operations (e.g., undelegations).
- **Consumer Initiated Slashing**: Enables the provider to jail validators for downtime infractions on the consumer chains. 
- **Reward Distribution**: Enables the consumers to transfer to the provider (over IBC) a portion of their block rewards as payment for the security provided. Once transferred, these rewards are distributed on the provider using the protocol in the [distribution module of Cosmos SDK](https://docs.cosmos.network/v0.45/modules/distribution/). 
- **Consumer Chain Removal**: Enables the provider to remove a consumer either after a `ConsumerRemovalProposal` passes governance or after one of the timeout periods elapses -- `InitTimeoutPeriod`, `VscTimeoutPeriod`, `IBCTimeoutPeriod`.
- **Social Slashing**: Equivocation offenses (double signing etc.) on consumer chains are logged, and then can be used in a governance proposal to slash the validators responsible.

In addition, RS has the following features:

- **Key Assignment**: Enables validator operators to use different consensus keys for each consumer chain validator node that they operate.
- **Jail Throttling**: Enables the provider to slow down a "worst case scenario" attack where a malicious consumer binary attempts to jail a significant amount (> 2/3) of the voting power, effectively taking control of the provider.
