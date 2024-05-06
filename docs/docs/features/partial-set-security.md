---
sidebar_position: 5
---

# Partial Set Security

Partial Set Security (PSS) allows consumer chains to leverage only a subset of validators from the provider chain, which offers more flexibility than the traditional Replicated Security model. By introducing the top_N parameter, each consumer chain can choose the extent of security needed:

    * Top N: Requires the top N% validators from the provider chain to secure the consumer chain. This guarantees that the validators with the most power on the provider will validate the consumer chain, while others can voluntarily opt in.

    * Opt-In: If the top_N parameter is set to zero, no validator is mandated to secure the consumer chain. Instead, any validator from the provider chain can opt in using a dedicated transaction.

:::tip
Partial Set Security is handled only by the provider chain - the consumer chains are simply sent validator sets, and they are not aware that this represents only a subset of the provider chains validator set.
:::

