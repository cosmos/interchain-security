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

# Cryptographic verification of equivocation
The Cryptographic verification of equivocation allows external agents to submit evidences of light client and double signing attack observed on a consumer chain. When a valid evidence is received, the malicious validators will be permanently jailed on the provider.

The feature is outlined in this [ADR-005](../adrs/adr-005-cryptographic-equivocation-verification.md)

By sending a `MsgSubmitConsumerMisbehaviour` or a `MsgSubmitConsumerDoubleVoting` transaction, the provider will
 verify the reported equivocation and, if successful, jail the malicious validator.

:::info
Note that this feature can only lead to the jailing of the validators responsible for an attack on a consumer chain. However, an [equivocation proposal](#double-signing-equivocation) can still be submitted to execute the slashing and the tombstoning of the a malicious validator afterwards. 
:::




