---
sidebar_position: 5
---

# Changeover Procedure

Chains that were not initially launched as consumers of replicated security can still participate in the protocol and leverage the economic security of the provider chain. The process where a standalone chain transitions to being a replicated consumer chain is called the **changeover procedure** and is part of the interchain security protocol. After the changeover, the new consumer chain will retain all existing state, including the IBC clients, connections and channels already established by the chain.

The relevant protocol specifications are available below:
* [ICS-28 with existing chains](https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/overview_and_basic_concepts.md#channel-initialization-existing-chains).
* [ADR in ICS repo](../adrs/adr-010-standalone-changeover.md)

## Overview

Standalone to consumer changeover procedure can rougly be separated into 4 parts:

### 1. ConsumerAddition proposal submitted to the `provider` chain
The proposal is equivalent to the "normal" ConsumerAddition proposal submitted by new consumer chains.

However, here are the most important notes and differences between a new consumer chain and a standalone chain performing a changeover:

* `chain_id` must be equal to the standalone chain id
* `initial_height` field has additional rules to abide by:

:::caution
```
{
...
    "initial_height" : {
        // must correspond to current revision number of standalone chain
        // e.g. stride-1 => "revision_number": 1
        "revision_number": 1,

        // must correspond to a height that is at least 1 block after the upgrade
        // that will add the `consumer` module to the standalone chain
        // e.g. "upgrade_height": 100 => "revision_height": 101
        "revision_height": 1,
    },
...
}
```
RevisionNumber: 0, RevisionHeight: 111
:::

* `genesis_hash` can be safely ignored because the chain is already running. A hash of the standalone chain's initial genesis may be used

* `binary_hash` may not be available ahead of time. All chains performing the changeover go through rigorous testing - if bugs are caught and fixed the hash listed in the proposal may not be the most recent one.

* `spawn_time` listed in the proposal MUST be before the `upgrade_height` listed in the the upgrade proposal on the standalone chain.
:::caution
`spawn_time` must occur before the `upgrade_height` on the standalone chain is reached becasue the `provider` chain must generate the `ConsumerGenesis` that contains the **validator set** that will be used after the changeover.
:::

* `unbonding_period` must correspond to the value used on the standalone chain. Otherwise, the clients used for the ccv protocol may be incorrectly initialized.

* `distribution_transmission_channel` **should be set**.

:::note
Populating `distribution_transmission_channel` will enable the standalone chain to re-use one of the existing channels to the provider for consumer chain rewards distribution. This will preserve the `ibc denom` that may already be in use.

If the parameter is not set, a new channel will be created.
:::

* `ccv_timeout_period` has no important notes

* `transfer_timeout_period` has no important notes

* `consumer_redistribution_fraction` has no important notes

* `blocks_per_distribution_transmission` has no important notes

* `historical_entries` has no important notes


### 2. upgrade proposal on standalone chain

The standalone chain creates an upgrade proposal to include the `interchain-security/x/ccv/consumer` module.

:::caution
The upgrade height in the proposal should correspond to a height that is after the `spawn_time` in the consumer addition proposal submitted to the `provider` chain.
:::

Otherwise, the upgrade is indistinguishable from a regular on-chain upgrade proposal.

### 3. spawn time is reached

When the `spawn_time` is reached on the `provider` it will generate a `ConsumerGenesis` that contains the validator set that will supercede the `standalone` validator set.

This `ConsumerGenesis` must be available on the standalone chain during the on-chain upgrade.

### 4. standalone chain upgrade

Performing the on-chain upgrade on the standalone chain will add the `ccv/consumer` module and allow the chain to become a `consumer` of replicated security.

:::caution
The `ConsumerGenesis` must be exported to a file called `genesis.json` and placed in the following folder on the standalone chain before the upgade: `<CURRENT_USER_DIR>/.sovereign/config/genesis.json` (`<CURRENT_USER>` is the home directory of the user executing the chain process)

The file must be placed at the exact specified location, otherwise the upgrade will not be executed correctly.
:::

After the `genesis.json` file has been made available, the process is equivalent to a normal on-chain upgrade. The standalone validator set will sign the next couple of blocks before transferring control to `provider` validator set.

The standalone validator set can still be slashed for any infractions if evidence is submitted within the `unboding_period`.

#### Notes

The changeover procedure may be updated in the future to create a seamless way of providing the validator set information to the standalone chain.

## Onboarding Checklist

This onboarding checklist is slightly different from the one under [Onboarding](./onboarding.md)

Additionally, you can check the [testnet repo](https://github.com/cosmos/testnets/blob/master/replicated-security/CONSUMER_LAUNCH_GUIDE.md) for a comprehensive guide on preparing and launching consumer chains.

## 1. Complete testing & integration

- [ ] test integration with gaia
- [ ] test your protocol with supported relayer versions (minimum hermes 1.4.1)
- [ ] test the changeover procedure
- [ ] reach out to the ICS team if you are facing issues

## 2. Create an Onboarding Repository

To help validators and other node runners onboard onto your chain, please prepare a repository with information on how to run your chain.

This should include (at minimum):

- [ ] genesis.json with CCV data (after spawn time passes)
- [ ] information about relevant seed/peer nodes you are running
- [ ] relayer information (compatible versions)
- [ ] copy of your governance proposal (as JSON)
- [ ] a script showing how to start your chain and connect to peers (optional)
- [ ] take feedback from other developers, validators and community regarding your onboarding repo and make improvements where applicable

Example of such a repository can be found [here](https://github.com/hyphacoop/ics-testnets/tree/main/game-of-chains-2022/sputnik).

## 3. Submit a ConsumerChainAddition Governance Proposal to the provider

Before you submit a `ConsumerChainAddition` proposal, please provide a `spawn_time` that is **before** the the `upgrade_height` of the upgrade that will introduce the `ccv module` to your chain.
:::danger
If the `spawn_time` happens after your `upgrade_height` the provider will not be able to communicate the new validator set to be used after the changeover.
:::

Additionally, reach out to the community via the [forum](https://forum.cosmos.network/) to formalize your intention to become an ICS consumer, gather community support and accept feedback from the community, validators and developers.

- [ ] determine your chain's spawn time
- [ ] determine consumer chain parameters to be put in the proposal
- [ ] take note to include a link to your onboarding repository

Example of a consumer chain addition proposal.

```js
// ConsumerAdditionProposal is a governance proposal on the provider chain to spawn a new consumer chain or add a standalone chain.
// If it passes, then all validators on the provider chain are expected to validate the consumer chain at spawn time.
// It is recommended that spawn time occurs after the proposal end time and that it is scheduled to happen before the standalone chain upgrade
// that sill introduce the ccv module.
{
    // Title of the proposal
    "title": "Changeover Standalone chain",
    // Description of the proposal
    // format the text as a .md file and include the file in your onboarding repository
    "description": ".md description of your chain and all other relevant information",
    // Proposed chain-id of the new consumer chain.
    // Must be unique from all other consumer chain ids of the executing provider chain.
    "chain_id": "standalone-1",
    // Initial height of new consumer chain.
    // For a completely new chain, this will be {0,1}.
    "initial_height" : {
        // must correspond to current revision number of standalone chain
        // e.g. standalone-1 => "revision_number": 1
        "revision_number": 1,

        // must correspond to a height that is at least 1 block after the upgrade
        // that will add the `consumer` module to the standalone chain
        // e.g. "upgrade_height": 100 => "revision_height": 101
        "revision_number": 1,
    },
    // Hash of the consumer chain genesis state without the consumer CCV module genesis params.
    // => not relevant for changeover procedure
    "genesis_hash": "d86d756e10118e66e6805e9cc476949da2e750098fcc7634fd0cc77f57a0b2b0",
    // Hash of the consumer chain binary that should be run by validators on standalone chain upgrade
    // => not relevant for changeover procedure as it may become stale
    "binary_hash": "376cdbd3a222a3d5c730c9637454cd4dd925e2f9e2e0d0f3702fc922928583f1",
    // Time on the provider chain at which the consumer chain genesis is finalized and all validators
    // will be responsible for starting their consumer chain validator node.
    "spawn_time": "2023-02-28T20:40:00.000000Z",
    // Unbonding period for the consumer chain.
    // It should should be smaller than that of the provider.
    "unbonding_period": 86400000000000,
    // Timeout period for CCV related IBC packets.
    // Packets are considered timed-out after this interval elapses.
    "ccv_timeout_period": 259200000000000,
    // IBC transfer packets will timeout after this interval elapses.
    "transfer_timeout_period": 1800000000000,
    // The fraction of tokens allocated to the consumer redistribution address during distribution events.
    // The fraction is a string representing a decimal number. For example "0.75" would represent 75%.
    // The reward amount distributed to the provider is calculated as: 1 - consumer_redistribution_fraction.
    "consumer_redistribution_fraction": "0.75",
    // BlocksPerDistributionTransmission is the number of blocks between IBC token transfers from the consumer chain to the provider chain.
    // eg. send rewards to the provider every 1000 blocks
    "blocks_per_distribution_transmission": 1000,
    // The number of historical info entries to persist in store.
    // This param is a part of the cosmos sdk staking module. In the case of
    // a ccv enabled consumer chain, the ccv module acts as the staking module.
    "historical_entries": 10000,
    // The ID of a token transfer channel used for the Reward Distribution
	// sub-protocol. If DistributionTransmissionChannel == "", a new transfer
	// channel is created on top of the same connection as the CCV channel.
	// Note that transfer_channel_id is the ID of the channel end on the consumer chain.
    // it is most relevant for chains performing a standalone to consumer changeover
    // in order to maintan the existing ibc transfer channel
    "distribution_transmission_channel": "channel-123"  // NOTE: use existing transfer channel if available
}
```

## 3. Submit an Upgrade Proposal & Prepare for Changeover

This proposal should add the ccv `consumer` module to your chain.

- [ ] proposal `upgrade_height` must happen after `spawn_time` in the `ConsumerAdditionProposal`
- [ ] advise validators about the exact procedure for your chain and point them to your onboarding repository


## 4. Upgrade time 🚀

- [ ] after `spawn_time`, request `ConsumerGenesis` from the `provider` and place it in `<CURRENT_USER_HOME_DIR>/.sovereign/config/genesis.json`
- [ ] upgrade the binary to the one listed in your `UpgradeProposal`

The chain starts after at least 66.67% of standalone voting power comes online. The consumer chain is considered interchain secured once the "old" validator set signs a couple of blocks and transfers control to the `provider` validator set.

- [ ] provide a repo with onboarding instructions for validators (it should already be listed in the proposal)
- [ ] genesis.json after `spawn_time` obtained from `provider` (MUST contain the initial validator set)
- [ ] maintenance & emergency contact info (relevant discord, telegram, slack or other communication channels)
