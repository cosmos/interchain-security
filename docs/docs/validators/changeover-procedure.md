---
sidebar_position: 4
---

# Validator Instructions for Changeover Procedure

More details available in [Changeover Procedure documentation](../consumer-development/changeover-procedure.md).

A major difference betwen launching a new consumer chain vs. onboarding a standalone chain to ICS is that there is no consumer genesis available for the standalone chain. Since a standalone chain already exists, its state must be preserved once it transitions to being a consumer chain.

## Timeline

Upgrading standalone chains can be best visualised using a timeline, such as the one available [Excalidraw graphic by Stride](https://app.excalidraw.com/l/9UFOCMAZLAI/5EVLj0WJcwt).

There is some flexibility with regards to how the changeover procedure is executed, so please make sure to follow the guides provided by the team doing the changeover.

![Standalone to consumer transition timeline](../../figures/ics_changeover_timeline_stride.png?raw=true)

### 1. `ConsumerAdditionProposal` on provider chain

This step will add the standalone chain to the list of consumer chains secured by the provider.
This step dictates the `spawn_time`. After `spawn_time` the CCV state (initial validator set of the provider) will be available to the consumer.

To obtain it from the provider use:
```bash
gaiad q provider consumer-genesis stride-1 -o json > ccv-state.json
jq -s '.[0].app_state.ccvconsumer = .[1] | .[0]' genesis.json ccv-state.json > ccv.json
```

### 2. `SoftwareUpgradeProposal` on the standalone/consumer chain

This upgrade proposal will introduce ICS to the standalone chain, making it a consumer.

### 3. Assigning a consumer key

After `spawn_time`, make sure to assign a consumer key if you intend to use one.

Instructions are available [here](../features/key-assignment.md)

### 4. Perform the software ugprade on standalone chain

Please use instructions provided by the standalone chain team and make sure to reach out if you are facing issues.
The upgrade preparation depends on your setup, so please make sure you prepare ahead of time.

:::danger
The `ccv.json` from step 1. must be made available on the machine running the standalone/consumer chain at standalone chain `upgrade_height`. This file contains the initial validator set and parameters required for normal ICS operation.

Usually, the file is placed in `$NODE_HOME/config` but this is not a strict requirement. The exact details are available in the upgrade code of the standalone/consumer chain.
:::

**Performing this upgrade will transition the standalone chain to be a consumer chain.**

After 3 blocks, the standalone chain will stop using the "old" validator set and begin using the `provider` validator set.

## FAQ

### Can I reuse the same validator key for the `consumer` chain that I am already using on the `standalone` chain? Will I need to perform a `AssignConsumerKey` tx with this key before spawn time?

Validators must either assign a key or use the same key as on the `provider`.

If you are validating both the `standalone` and the `provider`, you **can** use your current `standalone` key with some caveats:
* you must submit an `AssignConsumerKey` tx with your current `standalone` validator key
* it is best to submit `AssignConsumerKey` tx before `spawn_time`
* if you do not submit the Tx, it is assumed that you will be re-using your `provider` key to validate the `standalone/consumer` chain

### Can I continue using the same node that was validating the `standalone` chain?

Yes.

Please assign your consensus key as stated aboce.

### Can I set up a new node to validate the `standalone/consumer` chain after it transitions to replicated security?

Yes.

If you are planning to do this please make sure that the node is synced with `standalone` network and to submit `AssignConsumerKey` tx before `spawn_time`.


###  What happens to the `standalone` validator set after it after it transitions to replicated security?

The `standalone` chain validators will stop being validators after the first 3 blocks are created while using replicated security. The `standalone` validators will become **governors** and still can receive delegations if the `consumer` chain is using the `consumer-democracy` module.

**Governors DO NOT VALIDATE BLOCKS**.

Instead, they can participate in the governance process and take on other chain-specific roles.

## Credits
Thank you Stride team for providing detailed instructions about the changeover procedure.
