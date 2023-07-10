---
sidebar_position: 5
---

# Changeover Procedure

Chains that were not initially launched as consumers of replicated security can still participate in the protocol and leverage the economic security of the provider chain. The process where a sovereign chain transitions to being a replicated consumer chain is called the **changeover procedure** and is part of the interchain security protocol. After the changeover, the new consumer chain will retain all existing state, including the IBC clients, connections and channels already established by the chain.

The relevant protocol specification is available [here](https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/overview_and_basic_concepts.md#channel-initialization-existing-chains).

## Overview

Sovereign to consumer changeover procedure can rougly be separated into 4 parts:

### 1. ConsumerAddition proposal submitted to the `provider` chain
The proposal is equivalen to the "normal" ConsumerAddition proposal submitted by new consumer chains.

However, here are the most important notes and differences between a new consumer chain and a sovereign chain performing a changeover:

* `chain_id` must be equal to the sovereign chain id
* `initial_height` field has additional rules to abide by:

:::caution
```
{
...
    "initial_height" : {
        // must correspond to current revision number of sovereign chain
        // e.g. stride-1 => "revision_number": 1
        "revision_number": 1,

        // must correspond to a height that is at least 1 block after the upgrade
        // that will add the `consumer` module to the sovereign chain
        // e.g. "upgrade_height": 100 => "revision_height": 101
        "revision_height": 1,
    },
...
}
```
RevisionNumber: 0, RevisionHeight: 111
:::

* `genesis_hash` can be safely ignored because the chain is already running. A hash of the sovereign chain's initial genesis may be used

* `binary_hash` may not be available ahead of time. All chains performing the changeover go through rigorous testing - if bugs are caught and fixed the hash listed in the proposal may not be the most recent one.

* `spawn_time` listed in the proposal MUST be before the `upgrade_height` listed in the the upgrade proposal on the sovereign chain.
:::caution
`spawn_time` must occur before the `upgrade_height` on the sovereign chain is reached becasue the `provider` chain must generate the `ConsumerGenesis` that contains the **validator set** that will be used after the changeover.
:::

* `unbonding_period` must correspond to the value used on the sovereign chain. Otherwise, the clients used for the ccv protocol may be incorrectly initialized.

* `distribution_transmission_channel` **should be set**.

:::note
Populating `distribution_transmission_channel` will enable the sovereign chain to re-use one of the existing channels to the provider for consumer chain rewards distribution. This will preserve the `ibc denom` that may already be in use.

If the parameter is not set, a new channel will be created.
:::

* `ccv_timeout_period` has no important notes

* `transfer_timeout_period` has no important notes

* `consumer_redistribution_fraction` has no important notes

* `blocks_per_distribution_transmission` has no important notes

* `historical_entries` has no important notes


### 2. upgrade proposal on sovereign chain

The sovereign chain creates an upgrade proposal to include the `interchain-security/x/ccv/consumer` module.

:::caution
The upgrade height in the proposal should correspond to a height that is after the `spawn_time` in the consumer addition proposal submitted to the `provider` chain.
:::

Otherwise, the upgrade is indistinguishable from a regular on-chain upgrade proposal.

### 3. spawn time is reached

When the `spawn_time` is reached on the `provider` it will generate a `ConsumerGenesis` that contains the validator set that will supercede the `sovereign` validator set.

This `ConsumerGenesis` must be available on the sovereign chain during the on-chain upgrade.

### 4. sovereign chain upgrade

Performing the on-chain upgrade on the sovereign chain will add the `ccv/consumer` module and allow the chain to become a `consumer` of replicated security.

:::caution
The `ConsumerGenesis` must be exported to a file called `genesis.json` and placed in the following folder on the sovereign chain before the upgade: `<CURRENT_USER_DIR>/.sovereign/config/genesis.json` (`<CURRENT_USER>` is the home directory of the user executing the chain process)

The file must be placed at the exact specified location, otherwise the upgrade will not be executed correctly.
:::

After the `genesis.json` file has been made available, the process is equivalent to a normal on-chain upgrade. The sovereign validator set will sign the next couple of blocks before transferring control to `provider` validator set.

The sovereign validator set can still be slashed for any infractions if evidence is submitted within the `unboding_period`.

#### Notes

The changeover procedure may be updated in the future to create a seamless way of providing the validator set information to the sovereign chain.

## Onboarding Checklist
