---
sidebar_position: 2
title: ADR Template
---
# ADR [018]: [Fault Resolutions (fraud votes)]

## Changelog
* [date]: [changelog]

## Status


Proposed

## Context

Currently, in _PSS_, consumer chains can be secured by a only subset of the provider validator set.
 That makes them vulnerable to incorrect execution attacks. 
 These kind misbehaviour of that cannot be handled by the protocol and hence requires a way to submit evidence of such misbehaviour 
 to the Hub. 
 
 The ADR proposes a fault resolutions solution that gives the ability to the victims of these attack to prove and slash
 validators through a governance.



  from incorrect executions.  Partial Set Security gives the option to consumer chains to be secured by only a subset of the provider validator set.




> This section contains all the context one needs to understand the current state, and why there is a problem. It should be as succinct as possible and introduce the high level idea behind the solution. 

## Decision

> This section explains all of the details of the proposed solution, including implementation details.
It should also describe affects / corollary items that may need to be changed as a part of this.
If the proposed change will be large, please also indicate a way to do the change to maximize ease of review.
(e.g. the optimal split of things to do between separate PR's)

## Consequences

> This section describes the consequences, after applying the decision. All consequences should be summarized here, not just the "positive" ones.

### Positive

### Negative

### Neutral

## References

> Are there any relevant PR comments, issues that led up to this, or articles referenced for why we made the given design choice? If so link them here!

* [references]
