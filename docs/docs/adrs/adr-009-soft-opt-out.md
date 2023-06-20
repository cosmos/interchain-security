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

Some small validators may not have the resources needed to validate all consumer chains. Therefore a need exists to allow the bottom `x%` of validators to opt-out of validating a consumer chain. Meaning downtime infractions for these validators are dropped without ever reaching the provider.

This document specifies a modification to the ccv protocol which allows the bottom x% of the validator set by power to opt out of validating consumer chains without being jailed or otherwise punished for it. The feature is implemented with entirely consumer-side code.

## Decision

A consumer param exists, known as `SoftOptOutThreshold`, which is a string decimal in the range of [0, 0.2], that determines the portion of validators which are allowed to opt out of validating that specific consumer.

In every consumer beginblocker, a function is ran which determines the so called  _smallest non opt-out voting power_. Validators with voting power greater than or equal to this value must validate the consumer chain, while validators below this value may opt out of validating the consumer chain.

The smallest non opt-out voting power is recomputed every beginblocker in `UpdateSmallestNonOptOutPower()`. In a nutshell, the method obtains the total voting power of the consumer, iterates through the full valset (ordered power ascending) keeping track of a power sum, and when `powerSum / totalPower > SoftOptOutThreshold`, the `SmallestNonOptOutPower` is found and persisted.

Then, whenever the `Slash()` interface is executed on the consumer, if the voting power of the relevant validator being slashed is less than `SmallestNonOptOutPower` for that block, the slash request is dropped and never sent to the provider.

## Consequences

### Positive

* Small validators can opt out of validating specific consumers without being punished for it.

### Negative

* The bottom `x%` is still part of the total voting power of the consumer chain. This means that if the soft opt-out threshold is set to `10%` for example, and every validator in the bottom `10%` opts out from validating the consumer, then a `24%` downtime of the remaining voting power would halt the chain. This may be especially problematic during consumer upgrades.
* In nominal scenarios, consumers with soft opt out enabled will be constructing slash packets for small vals, which may be dropped. This is wasted computation, but necessary to keep implementation simple. Note that the sdk's [full downtime logic](https://github.com/cosmos/cosmos-sdk/blob/d3f09c222243bb3da3464969f0366330dcb977a8/x/slashing/keeper/infractions.go#L75) is always executed on the consumer, which can be computationally expensive and slow down certain blocks.

### Neutral

* Validators in the bottom of the valset who don't have to validate, may receive large delegation(s) which suddenly boost the validator to the subset that has to validate. This may catch the validator off guard.

## References

* Original issue with some napkin math [#784](https://github.com/cosmos/interchain-security/issues/784)
