---
sidebar_position: 3
---


# ICS Provider Proposals

Interchain security module introduces 3 new proposal types to the provider.

The proposals are used to propose upcoming interchain security events through governance.

## `ConsumerAdditionProposal`
:::info
If you are preparing a `ConsumerAdditionProposal` you can find more information in the [consumer onboarding checklist](../consumer-development/onboarding.md).
:::

Proposal type used to suggest adding a new consumer chain.

When proposals of this type are passed and the `spawn_time` specified in the proposal is reached, all provider chain validators are expected to run infrastructure (validator nodes) for the proposed consumer chain.

Minimal example:
```js
{
    // Time on the provider chain at which the consumer chain genesis is finalized and all validators
    // will be responsible for starting their consumer chain validator node.
    "spawn_time": "2023-02-28T20:40:00.000000Z",
    "title": "Add consumer chain",
    "description": ".md description of your chain and all other relevant information",
    "chain_id": "newchain-1",
    "initial_height" : {
        "revision_height": 0,
        "revision_number": 1,
    },
    // Unbonding period for the consumer chain.
    // It should should be smaller than that of the provider.
    "unbonding_period": 86400000000000,
    // Timeout period for CCV related IBC packets.
    // Packets are considered timed-out after this interval elapses.
    "ccv_timeout_period": 259200000000000,
    "transfer_timeout_period": 1800000000000,
    "consumer_redistribution_fraction": "0.75",
    "blocks_per_distribution_transmission": 1000,
    "historical_entries": 10000,
    "genesis_hash": "d86d756e10118e66e6805e9cc476949da2e750098fcc7634fd0cc77f57a0b2b0",
    "binary_hash": "376cdbd3a222a3d5c730c9637454cd4dd925e2f9e2e0d0f3702fc922928583f1"
}
```
More examples can be found in the replicated security testnet repository [here](https://github.com/cosmos/testnets/blob/master/replicated-security/baryon-1/proposal-baryon-1.json) and [here](https://github.com/cosmos/testnets/blob/master/replicated-security/noble-1/start-proposal-noble-1.json).

## `ConsumerRemovalProposal`
Proposal type used to suggest removing an existing consumer chain.

When proposals of this type are passed, the consumer chain in question will be gracefully removed from interchain security and validators will no longer be required to run infrastructure for the specified chain.
After the consumer chain removal, the chain in question will no longer be secured by the provider's validator set.

:::info
The chain in question my continue to produce blocks, but the validator set can no longer be slashed for any infractions committed on that chain.
Additional steps are required to completely offboard a consumer chain, such as re-introducing the staking module and removing the provider's validators from the active set.
More information will be made available in the [Consumer Offboarding Checklist](../consumer-development/offboarding.md).
:::

Minimal example:
```js
{
    // the time on the provider chain at which all validators are responsible to stop their consumer chain validator node
    "stop_time": "2023-03-07T12:40:00.000000Z",
    // the chain-id of the consumer chain to be stopped
    "chain_id": "consumerchain-1",
    "title": "This was a great chain",
    "description": "Here is a .md formatted string specifying removal details"
}
```

## `EquivocationProposal`
:::tip
`EquivocationProposal` will only be accepted on the provider chain if at least one of the consumer chains submits equivocation evidence to the provider.
Sending equivocation evidence to the provider is handled automatically by the interchain security protocol when an equivocation infraction is detected on the consumer chain.
:::

Proposal type used to suggest slashing a validator for double signing on consumer chain.
When proposals of this type are passed, the validator in question will be slashed for equivocation on the provider chain.

:::warning
Take note that an equivocation slash causes a validator to be tombstoned (can never re-enter the active set).
Tombstoning a validator on the provider chain will remove the validator from the validator set of all consumer chains.
:::

Minimal example:
```js
{
  "title": "Validator-1 double signed on consumerchain-1",
  "description": "Here is more information about the infraction so you can verify it yourself",
	// the list of equivocations that will be processed
  "equivocations": [
    {
        "height": 14444680,
        "time": "2023-02-28T20:40:00.000000Z",
        "power": 5500000,
        "consensus_address": "<consensus address ON THE PROVIDER>"
    }
  ]
}
```

### Notes
When submitting equivocation evidence through an `EquivocationProposal` please take note that you need to use the consensus address (`valcons`) of the offending validator on the **provider chain**.
Besides that, the `height` and the `time` fields should be mapped to the **provider chain** to avoid your evidence being rejected.

Before submitting the proposal please check that the evidence is not outdated by comparing the infraction height with the `max_age_duration` and `max_age_num_blocks` consensus parameters of the **provider chain**.

### Gaia example:
```
➜  ~ cat genesis.json | jq ".consensus_params"
{
  "block": {
    ...
  },
  "evidence": {
    "max_age_duration": "172800000000000",
    "max_age_num_blocks": "1000000",
    "max_bytes": "50000"
  },
  "validator": {
    ...
  },
  "version": {}
}
```

Any `EquivocationProposal` transactions that submit evidence with `height` older than `max_age_num_blocks` and `time` older than `max_age_duration` will be considered invalid.
