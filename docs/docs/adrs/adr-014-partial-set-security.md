---
sidebar_position: 2
title: ADR Template
---
# ADR XX: Partial Set Security

## Changelog

## Status

> A decision may be "proposed" if it hasn't been agreed upon yet, or "accepted" once it is agreed upon. If a later ADR changes or reverses a decision, it may be marked as "deprecated" or "superseded" with a reference to its replacement.

[Deprecated|Proposed|Accepted]

## Context

> This section contains all the context one needs to understand the current state, and why there is a problem. It should be as succinct as possible and introduce the high level idea behind the solution.

## Decision

### Partial Set Logic

This logic keeps a record of which validators are opted in to which consumer chains, and modifies valset updates accordingly.

The simplest part of this is to filter out the validators that are not opted into a given chain. But we also need to handle validators opting out of a consumer chain. In this case, it is not sufficient to simply filter them out of validator updates. A synthetic update must also be added to the valset update after they opt out, setting their power to 0 to remove them. Without this, they would continue at the power they had before opting out.

The partial set logic also needs to supply information on whether a validator is running on a given consumer chain, or was running on it during the unbonding period. This is used to determine whether a validator is liable for slashing on a given chain.

This is very similar to the key assignment logic, so we can copy concepts from it.

### Top N

The top-n percentage is a parameter that consumer chains can set that obligates the top "n" percent of the validator set to run their chain. There is some logic in the current consumer chain soft opt out code that could be useful to calculate which validators are in this top n.

This logic must be run periodically (probably every block), and figures out the set of validators which must be automatically opted in to each consumer chain depending on that consumer chain's top-n percentage. After this, the partial set state is updated accordingly.

### Downtime

Downtime needs to be handled differently depending on whether a validator is in the top-n of a consumer chain or not. When receiving a downtime packet, if the validator is in the top-n of the chain, it can be handled exactly as it is in RS, by jailing that validator.

If a validator is not in the top-n, they should simply be opted out of that consumer chain so that they are no longer in the validator set.

If the validator is not opted in to the consumer chain at all, obviously nothing should happen.

### Consumer addition

For consumer chains with no top-n, we will need to call the consumer chain creation logic from a message handler instead of a proposal handler. Further study is needed on the genesis and IBC client setup of such a chain. Doesn't seem like it is possible to start a chain with an empty validator set. Maybe the chain's creator can name an initial set. This doesn't obligate those validators to run the chain, but if they do, at least it can start. Projects would have to make out-of-band arrangements with their initial set.

We will also want to keep the proposal logic for consumer chains with a top-n, since this must be governance gated.

There will be some tricky edge cases around preventing squatting and griefing chain IDs.

- Governance gated top-n consumer chains should be able to overwrite the chain ID of a permissionless consumer chain.
- We may want to think about how to clean up consumer chains, in case someone is registering hundreds of chain IDs without running any real chains.

### Rewards

When rewards are received, they need to be allocated to the opted-in set of the consumer chain, instead of the whole Hub. Luckily this is easy with SDK 47.

## Consequences

> This section describes the consequences, after applying the decision. All consequences should be summarized here, not just the "positive" ones.

### Positive

### Negative

### Neutral

## References

> Are there any relevant PR comments, issues that led up to this, or articles referenced for why we made the given design choice? If so link them here!

- [references]
