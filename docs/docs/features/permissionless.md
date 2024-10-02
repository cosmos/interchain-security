---
sidebar_position: 7
---

# Permissionless ICS 

With the advent of Permissionless ICS, Opt In consumer chains can launch without going through governance.
However, Top N chains can only be launched through governance as a Top N chain requires the top N% of the provider validators to validate the chain.
In what follows, we explain the phases of a consumer chain and how we can launch a chain under Permissionless ICS.

:::tip
If you are preparing a new consumer chain you can find more information in the [consumer onboarding checklist](../consumer-development/onboarding.md).
:::

## From `chainId` to `consumerId`
With Permissionless ICS, anyone can issue a transaction to launch a consumer chain. As a result, the `chainId` of a consumer
chain cannot uniquely identify a consumer chain from the point of view of the provider, because we could have multiple
consumer chains with the exact same `chainId`.
Because of this, Permissionless ICS introduces the notion of a `consumerId`. The provider associates for each consumer chain
a unique `consumerId`. A consumer chain can then interact (e.g., update chain parameters) with its chain by utilizing this `consumerId`.
Additionally, validators can interact (e.g., assign a consumer key, opt in, etc.) with a consumer chain by using the consumer's `consumerId`.

## Phases of a Consumer Chain
A consumer chain can reside in one of the phases shown in the table below.

| **Phase**       | **Description**                                                                                                                                                |
|-----------------|----------------------------------------------------------------------------------------------------------------------------------------------------------------|
| **Registered**  | The consumer chain was created with `MsgCreateConsumer` and has received the consumer's associated `consumerId`. The chain cannot launch yet.                  |
| **Initialized** | The consumer chain has set all the initialization parameters and is ready to launch at `spawnTime`.                                                            |
| **Launched**    | The consumer chain has launched and is running. The provider chain is sending `VSCPacket`s to the consumer.                                                    |
| **Stopped**     | The consumer chain is stopped and the provider chain is not sending `VSCPacket`s to the consumer. The consumer chain is slated to be deleted.                  |
| **Deleted**     | The majority of the state of the consumer chain on the provider is deleted. Basic metadata of the consumer chain, such as the `chainId`, etc. are not deleted. |

The following diagram shows the phases and the actions that need to take place to move from one phase to another.

![phases of a consumer chain](../adrs/figures/adr19_phases_of_a_consumer_chain.png)

## Owner of a Consumer Chain
A consumer chain (either Opt In or Top N) has an owner.
An Opt In chain is owned by the address that initially sent and signed the `MsgCreateConsumer` message.
A Top N chain is owned by the governance module and can only be updated through governance proposals.

Note that the owner of a chain can be changed at any later point in time by providing a `new_owner_address` message
in the `MsgUpdateConsumer` message. As a result, an Opt In chain can change its owner to be the governance module
in order to transform to Top N chain, and a Top N chain can change its owner to something that is not the governance
module to become an Opt In chain (see [below](./permissionless.md#transform-an-opt-in-chain-to-top-n-and-vice-versa)).

## Launch an Opt In Chain
To launch an Opt In chain, we have to send a `MsgCreateConsumer` message. This message returns the newly created `consumerId`
associated with this consumer. The chain is considered to be in the registered phase at this point and its owner is the one
that signed the `MsgCreateConsumer` message.
If the optional `initialization_parameters` are provided in the `MsgCreateConsumer`, then the chain is considered to be in the
initialized phase and the chain can launch at the `spawnTime` provided in the `initialization_parameters`.

If no `initialization_parameters` are provided in `MsgCreateConsumer`, the consumer can later set those parameters
by issuing a `MsgUpdateConsumer`. The chain would then move to the initialized phase and be slated to launch.

:::info
An Opt In can only launch at `spawnTime` if at least one validator is opted in at `spawnTime`.
:::

## Launch a Top N Chain
To launch a Top N chain, we need to issue a `MsgCreateConsumer` to retrieve the `consumerId`. At this stage, the chain
corresponds to an Opt In chain and the owner of the chain is the one that signed the `MsgCreateConsumer`.
For the chain to become Top N we need to issue a message and a governance proposal:

1. A `MsgUpdateConsumer` message to change the owner of the chain to be that of the governance module, that is to `cosmos10d07y265gmmuvt4z0w9aw880jnsr700j6zn9kn`.
2. A governance proposal that includes a `MsgUpdateConsumer` that sets the `TopN` of the consumer chain.

:::warning
If `top_N`, `validators_power_cap`, or some other argument is not included in the power-shaping parameters, then it is considered
that the default value is set for this argument. For example, if a Top 50% chain wants to only modify `validators_power_cap`
from 35 to 40, then the power-shaping parameters in `MsgUpdateConsumer` still need to include that `top_N` is 50. Otherwise
`top_N` would be set to its default value of 0, and the chain would become an Opt-In chain.

To be **safe**, if you include power-shaping parameters in the `MsgUpdateConsumer`, always include `top_N` and all the power-shaping parameters.
The same applies for the initialization parameters.
:::

## Transform an Opt In Chain to Top N and Vice Versa
### From Opt In to Top N
This corresponds to the case of [launching a Top N chain](./permissionless.md#launch-a-top-n-chain). The Opt In chain
has to issue a `MsgUpdateConsumer` to change the owner of the consumer to be that of the governance module and
to issue a governance proposal that includes a `MsgUpdateConsumer` and sets the `TopN` of the consumer chain. 

### From Top N to Opt In
A consumer chain can move from Top N to Opt In by issuing a governance proposal that includes a `MsgUpdateConsumer`
that sets `TopN` to `0` and also sets the owner of the chain to not be the governance module anymore.

