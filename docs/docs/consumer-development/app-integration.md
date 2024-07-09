---
sidebar_position: 1
---
# Developing an ICS consumer chain

When developing an ICS consumer chain, besides just focusing on your chain's logic you should aim to allocate time to ensure that your chain is compatible with the ICS protocol.
To help you on your journey, the ICS team has provided multiple examples of a minimum viable consumer chain applications.

## Basic consumer chain

The source code for the example app can be found [here](https://github.com/cosmos/interchain-security/tree/main/app/consumer).

Please note that consumer chains do not implement the staking module - part of the validator set of the provider is replicated over to the consumer,
meaning that the consumer uses a subset of provider validator set and the stake of the validators on the provider determines their stake on the consumer.
Note that after the introduction of [Partial Set Security](../adrs/adr-015-partial-set-security.md), not all the provider validators have to validate a consumer chain (e.g., if `top_N != 100`).

Your chain should import the consumer module from `x/consumer` and register it in the correct places in your `app.go`.
The `x/consumer` module will allow your chain to communicate with the provider using the ICS protocol. The module handles all IBC communication with the provider, and it is a simple drop-in.
You should not need to manage or override any code from the `x/consumer` module.

## Democracy consumer chain

The source code for the example app can be found [here](https://github.com/cosmos/interchain-security/tree/main/app/consumer-democracy).

This type of consumer chain wraps the basic CosmosSDK `x/distribution`, `x/staking` and `x/governance` modules allowing the consumer chain to perform democratic actions such as participating and voting within the chain's governance system.

This allows the consumer chain to leverage those modules while also using the `x/consumer` module.

With these modules enabled, the consumer chain can mint its own governance tokens, which can then be delegated to prominent community members which are referred to as "representatives" (as opposed to "validators" in standalone chains). The token may have different use cases besides just voting on governance proposals.

## Standalone chain to consumer chain changeover

See the [standalone chain to consumer chain changeover guide](./changeover-procedure.md) for more information on how to transition your standalone chain to a consumer chain.

