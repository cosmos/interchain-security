---
sidebar_position: 1
---
# Developing an ICS consumer chain

When developing an ICS consumer chain, besides just focusing on your chain's logic you should aim to allocate time to ensure that your chain is compatible with the ICS protocol.
To help you on your journey, the ICS team has provided multiple examples of a minimum viable consumer chain applications.

## Basic consumer chain

The source code for the example app can be found [here](https://github.com/cosmos/interchain-security/tree/main/app/consumer).

Please note that consumer chains do not implement the staking module - the validator set is replicated from the provider, meaning that the provider and the consumer use the same validator set and their stake on the provider directly determines their stake on the consumer.
At present there is no opt-in mechanism available, so all validators of the provider must also validate on the provider chain.

Your chain should import the consumer module from `x/consumer` and register it in the correct places in your `app.go`.
The `x/consumer` module will allow your chain to communicate with the provider using the ICS protocol. The module handles all IBC communication with the provider, and it is a simple drop-in.
You should not need to manage or override any code from the `x/consumer` module.

## Democracy consumer chain

The source code for the example app can be found [here](https://github.com/cosmos/interchain-security/tree/main/app/democracy).

This type of consumer chain wraps the basic CosmosSDK `x/distribution`, `x/staking` and `x/governance` modules allowing the consumer chain to perform democratic actions such as participating and voting within the chain's governance system.

This allows the consumer chain to leverage those modules while also using the `x/consumer` module.

With these modules enabled, the consumer chain can mint its own governance tokens, which can then be delegated to prominent community members which are referred to as "representatives" (as opposed to "validators" in standalone chains). The token may have different use cases besides just voting on governance proposals.

## Standalone chain to consumer chain changeover

This feature is being actively worked on. Information will be provided at a later time.
