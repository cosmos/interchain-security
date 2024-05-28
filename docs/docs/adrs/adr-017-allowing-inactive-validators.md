---
sidebar_position: 18
title: Allowing validators outside the active set to validate on consumer chains
---
# ADR 017: Allowing validators outside the active set to validate on consumer chains

## Changelog
* 15th May 2024: Initial draft


## Status

Proposed

## Context

Currently, only validators in the active set on the provider can validate on consumer chains, which limits the number of validators that can participate in Interchain Security (ICS). 
Validators outside of the active set might be willing
to validate on consumer chains, but we might not want to make the provider validator set larger, e.g. to not put more strain on the consensus engine.
This runs the risk of leaving consumer chains with too few validators.

The purpose of this ADR is to allow validators that are *not* part of the consensus process on the provider chain (because they are inactive)
to validate on consumer chains.

In the context of this ADR, "consensus validator set" is the set of validators participating in the consensus protocol, and "staking validator set" is the set of validators viewed as active by the staking module.

Currently, the staking module, provider module, and CometBFT interact in this way:

![inactivevals_before.png](../../figures/inactivevals_before.png)

The staking module keeps a list of bonded validators. It sends these validators to CometBFT to inform which validators make up the next consensus validators, that is, the set of validators participating in the consensus process. Separately, the provider module reads the list of bonded validators and sends this to the consumer chain, after shaping it according to which validators are opted in and the parameters set by the consumer chain for allowlist, denylist, etc.

## Decision

The proposed solution to allow validators that are not participating in the consensus process on the provider (inactive validators) is to:

a) increase the number of bonded validators in the staking module to a large number, e.g. 500 (vs 180 today).
This would usually mean that all those 500 validators take part in the consensus process on the provider, and we do not want this (since it slows down consensus and dilutes rewards),
so to handle this, we also:

b) do *not* take the updates for CometBFT directly from the bonded validators in the staking module, and instead *filter* the bonded validators to send only the first `MaxProviderConsensusValidators` (sorted by largest amount of stake first) many validators to CometBFT. Practically, we achieve this by repurposing the provider module, reading the bonded validators from the staking module, and simply filtering that list before sending it to CometBFT.

Then lastly, we
c) use the enlarged list of bonded validators from the staking module as basis for the validator set that the provider module sends to consumer chains (again after applying power shaping and filtering out validatiors that are not opted in).

In consequence, the provider chain can keep a reasonably-sized validator set, while giving consumer chains a much larger pool of potential validators.

![inactivevals_after.png](../../figures/inactivevals_after.png)


Some additional considerations:

* Migration: In the migration, the last consensus validator set will be set to the last active validator set from the view of the staking module. Existing consumer chains are migrated to have a validator set size cap (otherwise, they could end up with a huge validator set including all the staking-but-not-consensus-active validators from the provider chain)
* Slashing: Validators that are not part of the active set on the provider chain can still be slashed for downtime on a consumer chain, but they *are not* slashed for downtime on the provider chain.
This is achieved without any additional changes to the slashing module, because the slashing module checks for downtime by looking at the consensus participants reported by CometBFT, and thus with the proposed solution, validators that are not part of the consensus validators on the provider chain are not considered for downtime slashing.
* Rewards: Validators that are not part of the active set on the provider chain can still receive rewards on the consumer chain, but they *do not* receive rewards from the provider chain. This change is
achieved without further changes to staking or reward distributions, because similar to downtime, rewards are based on the consensus validator set.

## Risk Mitigations

To mitigate risks from validators with little stake, we introduce a minimum stake requirement for validators to be able to validate on consumer chains, which can be set by each consumer chain independently, with a default value set by the provider chain.

Additional risk mitigations are to increase the active set size slowly, and to monitor the effects on the network closely. For the first iteration, we propose to increase the active set size to 200 validators (while keeping the consensus validators to 180), thus letting the 20 validators with the most stake outside of the active set validate on consumer chains.

## Consequences

### Positive

* Validators outside of the active set can validate on consumer chains without having an impact on the consensus engine of the provider chain
* Consumer chains can have a much larger validator set than the provider chain if they prefer this e.g. for decentralization reasons

### Negative

Allowing validators from the inactive set brings with it some additional risks.
In general, consumer chains will now face some of the problems also faced by standalone chains. It’s reasonable to assume that the validator set on the hub has a minimal amount of operational quality due to being battle tested and decentralized, and consumer chains with validators from outside the hub active set cannot rely on this as much anymore.

#### Sybil attacks

With the restricted size of the active set today, it’s clear that the set is at least minimally competitive and it is not trivial to spin up multiple nodes as a validator.

When we make the “potential validator set” much larger, we should assume that it becomes much less competitive to be part of that set, and thus trivial for single entities to control many of those validators.

#### Reputational damage is not a deterrent

For validators in the active set, we typically assume that if they would misbehave, they pay a large reputational cost. This represents delegators deciding to switch validators (potentially even on chains other than the one the misbehaviour happened on), and loss of credibility in the ecosystem. With the much larger active set, it seems prudent to assume that reputational damage is not a deterrent for many validators. They might only have minimal amounts of delegated stake and control most of it themselves, so they might not be deterred from performing actions that would usually bring reputational damage.

#### Additional negative consequences
* Validators outside of the active set become bonded, even if they are not validating on any consumer chains
* This will impact how future modules are integrated, since we will need to consider whether those modules should consider the consensus validators or the bonded validators (which other modules might assume to be the same)

### Neutral

## Alternative considerations

### Modifying the staking module

We could instead adapt the *staking module* with a similar change.
This might be better if it turns out that the staking module active set is used in many other places.

### Allowing unbonding validators to validate

Instead of increasing the active set size, we could allow validators that are unbonded (but still exist on the provider) to validate consumer chains.
For this, we would need to:
* Modify the VSC updates to consider the set of all validators, even unbonded ones, instead of just active ones
* Adjust our downtime jailing/equivocation slashing logic to work correctly with unbonded validators

## References

* [Security Aggregation](./adr-016-securityaggregation.md) has similar concerns where the staking validator set will differ from the consensus validator set
