---
sidebar_position: 2
title: Proof of Reputation Consumer Chains
---
# ADR 0XX: Proof of Reputation Consumer Chains 

## Changelog
* 2024-07-19: Initial draft of ADR

## Status

Proposed

## Context

Interchain Security (ICS) is a cross-chain staking protocol -- it uses the stake on the provider chain as collateral for the Proof of Stake (PoS) on the consumer chains. 
This means that the voting power of validators validating (aka producing blocks) on the consumer chains is a function of their stake on the provider.
Moreover, if these validators misbehave on the consumer chains, their stake on the provider is being slashed (see [ADR 005](./adr-005-cryptographic-equivocation-verification.md)). 
Thus, ICS consumer chains get their economical security from the provider.
However, this might come at a high cost.

### The Cost of PoS

One of the cost of validating on the consumer chains is operational -- validators need to run and monitor full nodes of every consumer chain they opt in. 
Although this cost varies from validator team to validator team (depending on how efficiently they can run their infrastructure), it doesn't depend on the total stake (or voting power) of the validators, so we can think of it as constant. 
The other cost of validating comes from the risk of getting slashed. 

Most chains in Cosmos (including the Cosmos Hub) use delelegated PoS -- users delegate their tokens to validators, which stake them in return for voting power. 
Therefore, validators act as representatives chosen by their delegators to represent their interests. 
When validators misbehave, their stake is getting slashed, including the tokes delegated by users. 
As validators don't need to have their own stake, delegators take the risk of validators misbehaving and having their assets slashed.

Misbehavior doesn't need to be malicious, e.g., most cases of double signing infractions are due to misconfiguration. 
This means that, by opting in on multiple consumer chains, validators increase their chances of getting slashed and, consequently, 
their delegators incur a higher risk. 
As a result, delegators want to be compensated for this additional risk, which makes PoS expensive. 

This ADR addresses the high cost of ICS by proposing the deployment of consumer chains that rely only on Proof of Reputation (PoR) -- when validators misbehave on these PoR consumer chains, their stake is not slashed, but they are tombstoned (permanently removed from the provider), which means their reputation is destroyed (they loose all their delegators). 

## Decision

To reduce the cost of ICS, consumer chains will be able to deploy as Proof of Reputation (PoR) chains.
This means that when validators that opt in misbehave on the consumer chains (e.g., they double sign), their stake on the provider is not being slashed, instead they are being tombstoned on the provider.
As a result, delegators incur no risk if their validators opt in on multiple PoR consumer chains.
This means that PoR consumer chains need only to cover the operational costs of the validators that opt in. 
For example, if we take `$600` as the cost of running a validator node, a budget of `$3000` will be sufficient to cover the cost of four validators running a PoR consumer chain and have `$150` profit per validator as incentive.   

### Security Model

The security model provided to PoR chains is based on the following properties of most Cosmos chains:

- validators are not anonymous, which means that they could be legally liable if they are malicious;
- the delegated PoS mechanism creates a reputation-based network of validators;
- most validators have most of their stake coming from delegations (i.e., nothing at stake, besides reputation);
- it is relatively difficult to enter the active validator set and even more so to climb the voting power ladder.

The assumption is that being permanently removed from the provider active validator set is strong enough of a deterrent to misbehaving on PoR consumer chains. 
Note that this assumption holds only if [inactive validators](./adr-017-allowing-inactive-validators.md) are ineligible to opt in on PoR consumer chains. 

The additional economical security a consumer gets from slashing is limited. 
The reason is that slashing punishes delegators as most of the stake is delegated.

One benefit of slashing is that it acts as a deterrent for someone buying a large amount of staking tokens in order to attack a consumer chain. 
For example, an attacker could get `$15.000.000` worth of ATOM, which would give them around `1%` voting power on the Cosmos Hub (at the time of this writing).
On a consumer chain, this voting power could be amplified depending on the other validators that opt in.
However, by having the right [power shaping](https://cosmos.github.io/interchain-security/features/power-shaping) settings, the voting power of validators can be capped. 
This means that even if the attacker manages to double sign without getting slashed, it doesn't benefit from this attack. 
Moreover, the attacker might lose due to other factors, such as [token toxicity](https://forum.cosmos.network/t/enabling-opt-in-and-mesh-security-with-fraud-votes/10901).  

### Implementation

The implementation of this feature involves the following steps:

- Add a field to `ConsumerAdditionProposal` to enable consumer chains to launch as PoR chains.
- Disable opt in to PoR consumer chains for validators outside of the provider's active set.
- Cryptographic equivocation evidence received for PoR chains results in the misbehaving validators only being tombstoned and not slashed.
- (Optional) PoR consumer chains can switch to PoS chains, but the transition takes at least unbonding period to allow for validators to opt out.    

## Consequences

### Positive

- Reduce the cost of ICS be removing the risk of slashing delegators.

### Negative

- Reduce the economical security provided to PoR consumer chains. 

### Neutral

- [Inactive validators](./adr-017-allowing-inactive-validators.md) are ineligible to opt in on PoR consumer chains

## References


