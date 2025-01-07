---
sidebar_position: 6
---

# Changeover Procedure

Chains that were **not** initially launched as consumers of Interchain Security can still participate in the protocol and leverage the economic security of the provider chain. The process where a standalone chain transitions to being a consumer chain is called the **changeover procedure** and is part of the Interchain Security protocol. After the changeover, the new consumer chain will retain all existing state, including the IBC clients, connections and channels already established by the chain.

The relevant protocol specifications are available below:
* [ICS-28 with existing chains](https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/overview_and_basic_concepts.md#channel-initialization-existing-chains).
* [ADR in ICS repo](../adrs/adr-010-standalone-changeover.md)

## Consumers on ICS Version `v6.4.0+`

For chains that are using ICS `v6.4.0` or newer, the standalone to consumer changeover consists of the following steps. 

### 1. Create a new consumer chain on the provider

Submit a `MsgCreateConsumer` message to the provider chain. This is a "normal" [MsgCreateConsumer message](../build/modules/02-provider.md#msgcreateconsumer) as described in the [onboarding checklist](./onboarding.md), but with the following important notes.

* `chain_id` **MUST** be equal to the standalone chain id.
* The consumer initialization parameters (i.e., `initialization_parameters`) must be adapted for the changeover procedure:
  
  * `initial_height` is not used as the provider uses an existing client of the standalone chain..
  * `spawn_time` is the time on the provider when the consumer module genesis state is being generated, 
  which means that at this time the provide creates the initial validator set that will validate the standalone chain once it becomes a consumer chain. 
  Consequently, `spawn_time` **MUST** occur before the standalone chain is upgraded and the consumer module is added as the upgrade requires the consumer module genesis state.
  * `unbonding_period` **MUST** correspond to the value used on the standalone chain.
  * `distribution_transmission_channel` **SHOULD** be set to the canonical IBC token transfer channel between the provider and the standalone chain. This will preserve the `ibc denom` that may already be in use.
  * `connection_id` **MUST** be set to the ID of the connection end on the provider chain on top of which the canonical IBC token transfer channel was created. 
  
### 2. Add consumer module to standalone chain 

The standalone chain **MUST** go through an upgrade to include the `x/ccv/consumer` module. 
Note that adding the `x/ccv/consumer` module requires the consumer module genesis state which is created by the provider at `spawn_time`.
Consequently, the `spawn_time` **MUST** occur before this upgrade. 

Note that the consumer module genesis state can be obtain from the provider using the [consumer genesis query](../build/modules/02-provider.md#consumer-genesis), i.e., 
```shell
interchain-security-pd query provider consumer-genesis [consumer-id] [flags]
```

The consumer genesis state must be exported to a file and placed in the correct folder on the standalone chain before the upgrade. 
The file must be placed at the exact specified location, otherwise the upgrade will not be executed correctly.
Usually the file is placed in `$NODE_HOME/config`, but the file name and the exact directory is dictated by the upgrade code on the `standalone` chain. 
Please check exact instructions provided by the `standalone` chain team.

After the `genesis.json` file has been made available, the process is equivalent to a normal on-chain upgrade. The standalone validator set will sign the next couple of blocks before transferring control to the initial ICS validator set.

Once upgraded, the `x/ccv/consumer` module will act as the "staking module" for the consumer chain, i.e., it will provide the validator set to the consensus engine. For staking a native token (e.g., for governance), the `x/ccv/democracy/staking` module allows the cosmos-sdk `x/staking` module to be used alongside the `x/ccv/consumer` module. For more details, check out the [democracy modules](../build/modules/04-democracy.md).

## Consumers on ICS Version `< v6.4.0`

Chains that are using older version of ICS (i.e., `< v6.4.0`), must "force" the provider to create a new client of the standalone chain (on top of which the CCV channel will be created). 
This is because older versions of the consumer module expects both a client state and a consensus state in order to create a new provider client. 
Therefore, when creating a new consumer chain on the provider, the following changes are necessary in the consumer initialization parameters:

* `connection_id` **MUST** be set to an empty string (i.e., `""`). As a result, the provider will create a new client of the consumer chain and a new connection on top of it.
* `initial_height` will be used by the provider when creating the new consumer client, so it **MUST** be set according to the following rules:
    ```json
    "initial_height" : {
        // must correspond to current revision number of standalone chain
        // e.g. stride-1 => "revision_number": 1
        "revision_number": 1,

        // must correspond to a height that is at least 1 block after the upgrade
        // that will add the `consumer` module to the standalone chain
        // e.g. "upgrade_height": 100 => "revision_height": 101
        "revision_height": 101,
    },
    ```

### Adapt the consumer module genesis state

Before the upgrade of the standalone chain (i.e., adding the `x/ccv/consumer` module), the consumer module genesis state created by the provider at `spawn_time` must be adapted to older versions of the consumer module. This consists of two changes.

First, by setting `connection_id` to an empty string, the provider will set the `preCCV` flag in the `ConsumerGenesisState` struct to `false`. This must be change to `true` in order to trigger the changeover procedure logic on the `x/ccv/consumer` module.

Second, the `connection_id` field of `ConsumerGenesisState` must be removed to enable older versions of the consumer module to unmarshal the consumer module genesis state obtained from the provider. This can be done using the `interchain-security-cd genesis transform` CLI command. 