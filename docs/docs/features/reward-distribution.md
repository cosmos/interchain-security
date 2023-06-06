---
sidebar_position: 2
---


# Reward distribution
Consumer chains have the option of sharing their block rewards (inflation tokens) and fees with provider chain validators and delegators.
In replicated security block rewards and fees are periodically sent from the consumer to the provider according to consumer chain parameters using an IBC transfer channel that gets created during consumer chain initialization.

Reward distribution on the provider is handled by the distribution module - validators and delegators receive a fraction of the consumer chain tokens as staking rewards.
The distributed reward tokens are IBC tokens and therefore cannot be staked on the provider chain.

Sending and distributing rewards from consumer chains to provider chain is handled by the `Reward Distribution` sub-protocol.

## Parameters
:::tip
The following chain parameters dictate consumer chain distribution amount and frequency.
They are set at consumer genesis and `blocks_per_distribution_transmission`, `consumer_redistribution_fraction`
`transfer_timeout_period` must be provided in every `ConsumerChainAddition` proposal.
:::


### `consumer_redistribution_fraction`
The fraction of tokens allocated to the consumer redistribution address during distribution events. The fraction is a string representing a decimal number. For example "0.75" would represent 75%.

:::tip
Example:

With `consumer_redistribution_fraction` set to `0.75` the consumer chain would send 75% of its block rewards and accumulated fees to the consumer redistribution address, and the remaining 25% to the provider chain fee pool every `n` blocks where `n == blocks_per_distribution_transmission`.
:::

### `blocks_per_distribution_transmission`
The number of blocks between IBC token transfers from the consumer chain to the provider chain.

### `transfer_timeout_period`
Timeout period for consumer chain reward distribution IBC packets.

### `distribution_transmission_channel`
Provider chain IBC channel used for receiving consumer chain reward distribution token transfers. This is automatically set during the consumer-provider handshake procedure.

### `provider_fee_pool_addr_str`
Provider chain fee pool address used for receiving consumer chain reward distribution token transfers. This is automatically set during the consumer-provider handshake procedure.
