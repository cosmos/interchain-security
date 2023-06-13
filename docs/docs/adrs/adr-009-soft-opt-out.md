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

- Validators subject to an equivocation proposal cannot finish unbonding
  their tokens before the end of the voting period.

### Negative

- A malicious consumer chain could forge slash packets enabling submission of
  an equivocation proposal on the provider chain, resulting in the freezing of
  validator's unbondings for an undeterminated amount of time.
- Misbehavior on a consumer chain can potentially go unpunished, if no one
  submits an equivocation proposal in time, or if the proposal doesn't pass.

### Neutral

- This feature can't be used for social slashing, because an equivocation
  proposal is only accepted if there's a slash log for the related
  validator(s), meaning the consumer chain has reported the equivocation to
  the provider chain.

## References

* https://github.com/cosmos/interchain-security/issues/747
* https://github.com/cosmos/interchain-security/pull/791
