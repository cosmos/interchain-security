---
sidebar_position: 4
---

# Consumer Initiated Slashing
A consumer chain is essentially a regular Cosmos-SDK based chain that uses the Interchain Security module to achieve economic security by stake deposited on the provider chain, instead of its own chain.
In essence, provider chain and consumer chains are different networks (different infrastructures) that are bound together by the provider's validator set. By being bound to the provider's validator set, a consumer chain inherits the economic security guarantees of the provider chain (in terms of total stake).

To maintain the proof of stake model, the consumer chain is able to send evidence of infractions (double signing and downtime) to the provider chain so the offending validators can be penalized.
Any infraction committed on any of the consumer chains is reflected on the provider and all other consumer chains.

In the current implementation there are two important changes brought by the Interchain Security module.

## Downtime Infractions

Downtime infractions are reported by consumer chains and are acted upon on the provider as soon as the provider receives the infraction evidence.

Instead of slashing, the provider will only jail offending validator for the duration of time established by the chain parameters.

:::info
[Slash throttling](../adrs/adr-002-throttle.md) (sometimes called jail throttling) mechanism ensures that only a fraction of the validator set can be jailed at any one time to prevent malicious consumer chains from harming the provider.
:::

## Equivocation Infractions

Equivocation infractions are reported by external agents (e.g., relayers) that can submit to the provider evidence of light client or double signing attacks observed on a consumer chain. 
The evidence is submitted by sending `MsgSubmitConsumerMisbehaviour` or `MsgSubmitConsumerDoubleVoting` transactions to the provider. 
When valid evidence is received, the malicious validators are slashed, jailed, and tombstoned on the provider.
This is enabled through the _cryptographic verification of equivocation_ feature. 
For more details, see [ADR-005](../adrs/adr-005-cryptographic-equivocation-verification.md) and [ADR-013](../adrs/adr-013-equivocation-slashing.md).

### Report equivocation infractions through CLI

The ICS provider module offers two commands for submitting evidence of misbehavior originating from a consumer chain.
Below are two examples illustrating the process on Cosmos Hub. 

Use the following command to submit evidence of double signing attacks:
```bash
gaiad tx provider submit-consumer-double-voting [path/to/evidence.json] [path/to/infraction_header.json] --from node0 --home ../node0 --chain-id $CID 
```

Use the following command to submit evidence of light client attacks:
```bash
gaiad tx provider submit-consumer-misbehaviour [path/to/misbehaviour.json] --from node0 --home ../node0 --chain-id $CID
```

### Report equivocation infractions with Hermes

Ensure you have a well-configured Hermes `v1.7.3+` relayer effectively relaying packets between a consumer chain and a provider chain. 
The following command demonstrates how to run a Hermes instance in _evidence mode_ to detect misbehaviors on a consumer chain and automatically submit the evidence to the provider chain.
```bash
hermes evidence --chain <CONSUMER-CHAIN-ID>
```

:::tip
`hermes evidence` takes a `--check-past-blocks` option giving the possibility to look for older evidences (default is 100).
:::