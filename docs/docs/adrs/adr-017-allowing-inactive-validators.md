---
sidebar_position: 18
title: ADR Template
---
# ADR [17]: [Allowing validators outside the active set to validate on consumer chains]

## Changelog

## Status

Proposed

## Context

Currently, only validators in the active set on the provider can validate on consumer chains.
This limits the number of validators that can validate on consumer chains. Validators outside of the active set might be willing
to validate on consumer chains, but we might not want to make the provider validator set larger, e.g. to not put more strain on the consensus engine.
This runs the risk of leaving consumer chains with too few validators.

The purpose of this ADR is to allow validators that are *not* part of the consensus process on the provider chain (because they are inactive)
to validate on consumer chains.

## Decision

The proposed solution is to:
* Increase the validator set size in the staking module to a very large number (e.g. 500)
* Introduce an additional parameter in the provider module, called MaxProviderConsensusValidators
* When the validator updates are passed to the consensus engine of the provider during EndBlock, the provider module will simply only pass the first MaxProviderConsensusValidators validators by voting power to the consensus engine

To facilitate this, the provider module will need to:
* keep the last validator set sent to the consensus engine
* load the current validator set from the staking module
* diff the two sets, and send the diff to the consensus engine

Extra considerations:
* Migration: In the migration, the last consensus validator set would just be sent to the last active validator set from the view of the staking module. Existing consumer chains need to be migrated to have a validator set size cap (otherwise, they could end up with a huge validator set including all the staking-but-not-consensus-active validators from the provider chain)
* Slashing: Validators that are not part of the active set on the provider chain can still be slashed on the consumer chain, but they *should not* be slashed for downtime on the provider chain. Will those validators accrue missed blocks? If yes, we probably need to make changes in the slashing module to not continuously slash them for downtime on the provider
* Rewards: Validators that are not part of the active set on the provider chain can still receive rewards on the consumer chain, but they *should not* receive rewards on the provider chain.
* Where else might the staking module validators be used? We need to carefully assess whether we need to change these references and direct them to the "actual active set" of the provider chain instead, or whether they can still go to the staking module

Comms:
* This change needs to be communicated, in particular to frontends. They need to be aware that there is a difference between "active validator on the provider chain", and "part of the consensus validator set on the provider chain".

## Consequences

### Positive

* Validators outside of the active set can validate on consumer chains without having an impact on the consensus engine of the provider chain
* We can do this change without further forking from the standard Cosmos SDK modules

### Negative

* We need to be very careful in making sure all existing references to the validator set are updated to refer to the "actual active set" of the provider chain if necessary
* In the worst case, this might mean we need many changes to existing Cosmos SDK modules (and this would negate one of the positives of this solution)

### Neutral

## Alternative considerations

We could instead adapt the *staking module* with a similar change.
This might be better if it turns out that the staking module active set is used in many other places.

## References

* [adr-016-securityaggregation.md] has similar concerns where the staking validator set will differ from the consensus validator set
* 
