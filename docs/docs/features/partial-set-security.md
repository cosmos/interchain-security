---
sidebar_position: 6
---

# Partial Set Security

Partial Set Security (PSS) is a complete revamp of the Hub's security offering. It allows consumer chains to leverage only a subset of validators from the provider chain, which offers more flexibility than the previous Replicated Security model. By introducing the top_N parameter, each consumer chain can choose the extent of security needed:

    * Top N: Requires the top N% validators from the provider chain to secure the consumer chain. This guarantees that the validators with the most power on the provider will validate the consumer chain, while others can voluntarily opt in.

    * Opt-In: If the `top_N` parameter is set to zero, no validator is mandated to secure the consumer chain. Instead, any validator from the provider chain can opt in using a dedicated transaction.

An advantage of a Top N chain is that the consumer chain is guaranteed to receive at least a certain fraction of the market cap of the provider chain in security. In turn, this chain needs to be approved by governance, since validators will be forced to run the chain. Thus, Top N chains should typically expect to need to provide a strong case for why they should be added to the provider chain, and they should make sure they offer enough rewards to incentivize validators and delegators to vote for their proposal.

Opt-In chains, on the other hand, are more flexible. Validators are never forced to validate these chains and simply opt in if they want to. At the moment, opt-in chains still require a governance proposal, but this will be removed in the next release, allowing chains to launch completely permissionlessly. However, opt in chains do not get a fixed amount of security as a relation of the market cap of the provider as top N chains do, so opt in chains might want to keep an eye on how many validators have opted in to validate their chain and adjust their reward emissions accordingly to incentivize validators.

:::tip
Partial Set Security is handled only by the provider chain - the consumer chains are simply sent validator sets, and they are not aware that this represents only a subset of the provider chain's validator set.
:::

:::caution

Top N chains always require a governance proposal because they force the top N
validators to run the chain.

As a temporary measure, Opt In chains also require a governance proposal, but this will be removed in the next release, making Opt In chains completely permissionless.

The reason Opt In chains currently require a governance prop is to prevent issues around chain ID squatting, i.e. someone could spuriously register many desirable chain IDs of upcoming consumer chain and simply deny legitimate consumer chains from using them. The plan is to allow launching Opt In chains permissionlessly without going through governance, with quality control being handled by the market of validators deciding which chains they would like to validate on.
:::

:::tip
A running Top N consumer chain might want to become an Opt-In chain or vice versa. This can be achieved by issuing
a [`ConsumerModificationProposal`](./proposals.md#consumermodificationproposal).
:::
