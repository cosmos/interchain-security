---
sidebar_position: 21
title: Customizable Slashing and Jailing
---
# ADR 020: Customizable Slashing and Jailing

## Changelog
* 2024-07-19: Initial draft of ADR

## Status

Proposed

## Context

Interchain Security (ICS) is a cross-chain staking protocol -- it uses the stake on the provider chain as collateral for the Proof of Stake (PoS) on the consumer chains. 
This means that the voting power of validators validating (aka producing blocks) on the consumer chains is a function of their stake on the provider.
Moreover, if these validators misbehave on the consumer chains, they get punished on the provider chain. 
ICS is currently differentiating between two types of infractions -- equivocation and downtime. 
Depending on the infraction type, the misbehaving validators might be jailed (i.e., removed from the provider validator set) and / or slashed (i.e., a portion of their stake on the provider is being burned).
For example, validators double sining on consumer chains get slashed and are permanently jailed, 
while validators not validating sufficient blocks are temporarily jailed.

This means that ICS consumer chains get their economical security from the provider.
However, this might come at a high cost.

### The Cost of PoS

One of the cost of validating on the consumer chains is operational -- validators need to run and monitor full nodes of every consumer chain they opt in for. 
Although this cost varies from validator team to validator team (depending on how efficiently they can run their infrastructure), it doesn't depend on the total stake (or voting power) of the validators, so we can think of it as constant. 
The other cost of validating comes from the risk of getting slashed or jailed.

Most chains in Cosmos (including the Cosmos Hub) use delegated PoS -- users delegate their tokens to validators, which stake them in return for voting power. 
Therefore, validators act as representatives chosen by their delegators to represent their interests. 
However, delegators share the risk of their validators getting slashed or jailed:

- When validators get slashed, a portion of their stake is being burned, including a portion of the tokens delegated by users.
  As validators don't need to have their own stake, it is possible that delegators take all the risk of validators misbehaving and having their assets slashed.
- When validators get jailed, they no longer receive block rewards (neither from the provider nor from the consumer chains). 
  This applies also for their delegators. 
  As a result, delegators might choose to restake their tokens with another validator.
  The longer the validators are jailed, the more likely is that delegators will restake.
  Thus, by getting jailed, validators risk damaging their reputation. 

Misbehavior doesn't need to be malicious, e.g., most cases of double signing infractions are due to misconfiguration. 
This means that, by opting in on multiple consumer chains, validators and their delegators incur a higher risk.
As a result, validators and their delegators want to be compensated for this additional risk, which makes the current design of ICS expensive. 

This ADR addresses the high cost of ICS by allowing consumer chains to customize the slashing and jailing conditions. 
Basically, every consumer chain can decide the punishment for every type of infraction. 
This enables consumer chains to tradeoff economical security against cost.  

## Decision

To reduce the cost of ICS, consumer chains will be able to customize the slashing and jailing for every type of infraction. 


deploy as Proof of Reputation (PoR) chains.
This means that when validators that opt in misbehave on the consumer chains (e.g., they double sign), their stake on the provider is not being slashed, instead they are being tombstoned on the provider.
As a result, delegators incur (almost) no risk if their validators opt in on multiple PoR consumer chains.
If their validators are tombstoned, then the delegators can redelegate to other validators. 
However, delegators cannot redelegate multiple times, which means that if the new validators get also tombstoned, the delegators need to wait for the unbonding period to elapse. 

This means that PoR consumer chains need only to cover the operational costs of the validators that opt in. 
For example, if we take `$600` as the cost of running a validator node, a budget of `$3000` will be sufficient to cover the cost of four validators running a PoR consumer chain and have `$150` profit per validator as incentive.
In practice, this can be implemented via the per-consumer-chain commission rate that allows validators to have different commission rates on different consumer chains. 

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
This means that even if the attacker manages to double sign without getting slashed, as long as they don't have 1/3+ of the voting power, they cannot benefit from the attack. 
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


