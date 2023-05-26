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

(Copied from [#747](https://github.com/cosmos/interchain-security/issues/747))

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

These methods use a counter under the hood, which means we can use them without 
conflicts with the *Completion of Unbonding Operations* system. Giving an
unbonding period (already paused by definition because of the *Completion of
Unbonding Operations* system), an additional pause will just increase the
counter, so when this unbonding period has reached its maturity on provider
and all consumer chains, it will remain paused.

### When pause

The unbonding period (if there is any unbonding) should be paused once an
equivocation proposal enters the voting period. For that, the `gov` module's
hook `AfterProposalDeposit` can be used. 

If the hook is triggered with a an equivocation proposal in voting period, then
for each equivocation of the proposal, the related unbonding operations of the
related validator must be paused.

Note that even after the voting period has started, a proposal can receive
additional deposits. The hook is triggered however at arrival of a deposit, so
a check to verify that the proposal is not already in voting period is
required.

### When unpause

We can use a `gov` module's hook also here and it is
`AfterProposalVotingPeriodEnded`.

If the hook is triggered with an equivocation proposal, then for each
equivocation, unpause all unbonding operations of the related validator.

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
