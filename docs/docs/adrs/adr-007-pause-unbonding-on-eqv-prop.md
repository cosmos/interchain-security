---
sidebar_position: 2
title: ADR Template
---
# ADR 007: Pause validator unbonding during equivocation proposal

## Changelog
* 2023-05-16: Initial Draft

## Status

Proposed

## Context

Currently, if an equivocation slashing proposal is created after more than one
week has passed since the equivocation, it is possible that the validator in
question could unbond and get away without being slashed, since the unbonding
period is 3 weeks, and the voting period is 2 weeks. For this reason, it might
be good to pause unbondings for validators named in an equivocation slashing
proposal until the proposal's voting period is over.

## Decision

### How

Pausing the unbonding period is already possible thanks to the changes in the
`staking` module of the cosmos-sdk:
- `stakingKeeper.PutUnbondingOnHold` pauses an unbonding period
- `stakingKeeper.UnbondingCanComplete` unpauses an unbonding period

These methods use a reference counter under the hood, that gets incremented
every time `PutUnbondingOnHold` is called, and decreased when
`UnbondingCanComplete` is called instead. A specific unbonding is considered
fully unpaused when its underlying reference counter reaches 0. Therefore, as
long as we safeguard consistency - i.e. we make sure we eventually decrement
the reference counter for each time we have incremented it - we can safely use
this existing mechanism without conflicts with the *Completion of Unbonding
Operations* system.

### When pause

The unbonding period (if there is any unbonding) should be paused once an
equivocation proposal enters the voting period. For that, the `gov` module's
hook `AfterProposalDeposit` can be used. 

If the hook is triggered with a an equivocation proposal in voting period, then
for each equivocation of the proposal, the unbonding operations of the related
validator that were initiated after the equivocation block time must be paused
- i.e. the underlying reference counter has to be increased.

Note that even after the voting period has started, a proposal can receive
additional deposits. The hook is triggered however at arrival of a deposit, so
a check to verify that the proposal is not already in voting period is
required.

### When unpause

We can use a `gov` module's hook also here and it is
`AfterProposalVotingPeriodEnded`.

If the hook is triggered with an equivocation proposal, then for each
associated equivocation, the unbonding operations of the related validator that
were initiated between the equivocation block time and the start of the
proposal voting period must be unpaused - i.e. decrease the underlying
reference counter - regardless of the proposal outcome.

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
