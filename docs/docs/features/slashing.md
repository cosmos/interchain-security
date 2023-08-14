---
sidebar_position: 4
---

# Consumer Initiated Slashing
A consumer chain is essentially a regular Cosmos-SDK based chain that uses the interchain security module to achieve economic security by stake deposited on the provider chain, instead of its own chain.
In essence, provider chain and consumer chains are different networks (different infrastructures) that are bound together by the provider's validator set. By being bound to the provider's validator set, a consumer chain inherits the economic security guarantees of the provider chain (in terms of total stake).

To maintain the proof of stake model, the consumer chain is able to send evidence of infractions (double signing and downtime) to the provider chain so the offending validators can be penalized.
Any infraction committed on any of the consumer chains is reflected on the provider and all other consumer chains.

In the current implementation there are 2 important changes brought by the interchain security module:

## Downtime infractions
reported by consumer chains are acted upon on the provider as soon as the provider receives the infraction evidence.

Instead of slashing, the provider will only jail offending validator for the duration of time established in the chain parameters.

:::info
Slash throttling (sometimes called jail throttling) mechanism ensures that only a fraction of the validator set can be jailed at any one time to prevent malicious consumer chains from harming the provider.
:::

## Double-signing (equivocation)
infractions are not acted upon immediately.

Upon receiving double signing evidence, the provider chain will take note of the evidence and allow for `EquivocationProposal` to be submitted to slash the offending validator.
Any `EquivocationProposal`s to slash a validator that has not double signed on any of the consumer chains will be automatically rejected by the provider chain.

:::info
The offending validator will only be slashed (and tombstoned) if an `EquivocationProposal` is accepted and passed through governance.

The offending validator will effectively get slashed and tombstoned on all consumer chains.
:::

<!-- markdown-link-check-disable-next-line -->
You can find instructions on creating `EquivocationProposal`s [here](./proposals#equivocationproposal).
