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

# Cryptographic verification of equivocation and slashing
The Cryptographic verification of equivocation allows external agents to submit evidences of light client and double signing attack observed on a consumer chain. When a valid evidence is received, the malicious validators will be slashed, jailed, and tombstoned on the provider.

The feature is outlined in [ADR-005](../adrs/adr-005-cryptographic-equivocation-verification.md) and [ADR-013](../adrs/adr-013-equivocation-slashing.md).

By sending a `MsgSubmitConsumerMisbehaviour` or a `MsgSubmitConsumerDoubleVoting` transaction, the provider will
 verify the reported equivocation and, if successful, slash, jail, and tombstone the malicious validator.