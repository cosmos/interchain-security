---
sidebar_position: 10
title: Soft Opt-Out
---
## ADR 009: Soft Opt-Out

## Changelog

* 6/13/23: Initial draft of ADR. Feature already implemented and in production.

## Status

Accepted

## Context

Some small validators may not have the resources needed to validate all consumer chains. Therefore a need exists to allow the bottom _% of validators to opt-out of validating a consumer chain. Meaning downtime infractions for relevant validators are dropped on the provider.

This document specifies a modification to the ccv protocol which allows the bottom x% of the validator set by power to opt out of validating consumer chains without being jailed or otherwise punished for it. The feature is implemented with entirely consumer-side code.

## Decision

A param exists, known as `SoftOptOutThreshold`, which is a string decimal in the range of [0, 0.2], that determines the portion of validators which are allowed to opt out of validating consumers.

Every beginblocker, a function is ran which determines the voting power s.t. any validator with greater than or equal to said voting power must validate all consumers. Any validator with less than said voting power may opt out of validating any consumer chain.

The voting power value described above is referred to in code as "smallest non opt out power". The value is recomputed every beginblocker in `UpdateSmallestNonOptOutPower()`. In a nutshell, the method obtains the total voting power of the chain, iterates through the full valset (ordered power ascending) keeping track of a power sum, and when `powerSum / totalPower > SoftOptOutThreshold`, the `SmallestNonOptOutPower` is found and persisted.

Then, whenever the provider receives a slash packet and that packet is handled, if the voting power of the relevant validator being slashed is less than `SmallestNonOptOutPower` for that block, the slash request is dropped.

## Consequences

### Positive

* Small validators can opt out of validating consumers without being punished for it.

### Negative

* Small validators who are not being slashed will still be present in the validator set of the consumer chain. In other words, we are sacrificing liveness, not safety. The economic security of the consumer chain is the same, but consumers may be more likely to halt. If soft opt out threshold is set to 10% for example, and every validator who doesn't have to validate the consumer doesn't validate it, then 23% downtime of the remaining valset could halt the chain. This may manifest in slightly longer downtime periods during upgrades.

### Neutral

* In nominal scenarios, consumers will be sending slash packets for small vals, which may be dropped by the provider. This is wasted computation, but necessary to keep implementation simple.
* Validators in the bottom of the valset who don't have to validate, may receive large delegation(s) which suddenly boost the validator to the subset that has to validate. This may catch the validator off guard.

## References

* Original issue with some napkin math [#784](https://github.com/cosmos/interchain-security/issues/784)
