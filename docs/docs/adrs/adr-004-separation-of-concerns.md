---
sidebar_position: 4
title: Separating consumer and provider libraries
---
# ADR 004: Separating consumer and provider libraries

## Changelog

* 2023-04-27: Initial draft
* 2023-04-28: Changed content to reflect new approach

## Status

> A decision may be "proposed" if it hasn't been agreed upon yet, or "accepted" once it is agreed upon. If a later ADR changes or reverses a decision, it may be marked as "deprecated" or "superseded" with a reference to its replacement.

Proposed

## Context

The main deliverable for interchain-security are consumer and provider libraries that are currently located in `x/ccv/provider` and `x/ccv/consumer`.
Any blockchain applications (`app.go`s) available in the interchain-security repository are used for testing purposes only and should be viewed as examples for building chains implementing ICS.

By cosmos-sdk terminology and conventions, all applications in the interchain-security repos are just `simapp`s:

* `interchain-security-pd` is a `simapp` for testing the provider ICS library
* `interchain-security-cd` is a `simapp` for testing the consumer ICS library

Any apps existing in the interchain-security repository should not be considered as deliverables as they are not intended to be used by ICS customers, aside from usage in e2e testing frameworks.

Developers of ICS have found it difficult to reason about semantic versioning within this repository. The main reason for this is that the provider and consumer libraries are not separated. Ie. they share a single `go.mod`, and therefore abide by the same dependencies and release cycle. This means that any change to the provider library affects the consumer library and vice versa. A single release cycle for ICS does not properly communicate if changes were made to the provider library, consumer library, or both.

Splitting consumer and provider libraries enables separate release cycles and makes development easier while maintaining provider and consumer compatibility.

## Proposal

We're proposing the addition of three new `go.mod`s for all of `x/ccv/provider`, `x/ccv/consumer`, `x/ccv/types`. Where the types module does not depend on any other module from ICS, and the provider and consumer modules depend on ONLY the types module. The existing top level `go.mod` will remain in the repo, but will only be used for testing purposes. The top level `go.mod` will naturally depend on all three of the other modules.

## Handling shared functionality

At present provider and consumer libraries share some functionality, type, interfaces and constants.

Most of the shared functionality comes from the fact that the provider chain has to communicate the initial validator set to the consumer so that the consumer can include it in its genesis.json (consumer has to know the state of the provider's validator set when the first consumer block is produced). The remainder of shared functionality comprises ICS messaging types and their validation.

The shared code between provider and consumers is currently the `x/ccv/types` directory, and should really only be used internally to this repo. In the scenario that code is changed in the `x/ccv/types` directory, that module version can be bumped for internal use, and the provider and consumer libraries can be bumped to use the new version as needed.

### QA considerations

We rely on the QA process to assure that provider and consumer are compatible, and that we have a sane and organized way to isolate patches to an ICS version running in production (whether that be for providers or consumers).

Since emergency releases do happen (as has been shown with dragonberry and changes in ICS regarding consumer chain removals) we cannot simply ignore the systemic risk they introduce. Our workflows must be adapted in a way that accounts for emergency scenarios, to the best of our ability.

We believe that separating provider and consumer versioning with separated `go.mod`s is the best way to easily reason about what feature/fixes affect consumers, providers, or both.

## Steps to perform

Do some refactors, but keep x/ccv as minimally changed as possible.

1. Refactor `x/ccv/types` s.t. it doesn't have package dependencies from this repo. Make the types folder the lowest level of dependency. Make sure `x/ccv/types` only contains code that is shared by consumer/provider (including .pb files, this will require some changes to .proto files).
2. Refactor `x/ccv/provider` and `x/ccv/consumer` s.t. they only rely on `x/ccv/types`, not one another, and not any other packages from this repo (not even `testutils/` for example). I've confirmed this is possible.
3. Add three new `go.mod`s for all of `x/ccv/provider`, `x/ccv/consumer`, `x/ccv/types`, module import dependencies match what's described in previous steps.
4. Split out `make proto-gen` into `make proto-gen-provider`, `make proto-gen-consumer`, and `make proto-gen-types`. This is necessary since `make proto-gen` would be responsible for generating .pb files to 3 different submodules, each of which could require different protobuf build tooling (due to reliance on sdk 45 vs sdk 47 for example).

## Decision

> This section explains all of the details of the proposed solution, including implementation details.
It should also describe affects / corollary items that may need to be changed as a part of this.
If the proposed change will be large, please also indicate a way to do the change to maximize ease of review.
(e.g. the optimal split of things to do between separate PR's)

Decision not yet reached

## Consequences

> This section describes the consequences, after applying the decision. All consequences should be summarized here, not just the "positive" ones.

### Positive

* Less refactoring than initial idea.
* We will rarely need to release new versions for `x/ccv/types`, and if we do, it would truly be a change that is relevant to both consumer and provider. A version bump to `x/ccv/types` does not necessarily mean both consumer and provider must immediately upgrade to the new version tho, take sdk upgrade as example.
* The association between changes in `x/ccv` and whether this affects consumer/provider is very clear. Semantic versioning for consumer and provider actually means something. Emergency patches to specific versions of consumer/provider module are easier to execute and keep track of.

### Negative

* More work having to do .pb file generation compared to initial idea.
* There are situations where certain branches of ICS would not be able to execute one or multiple of the 3 make proto-gen-______ options without breaking code.

### Neutral


## References

> Are there any relevant PR comments, issues that led up to this, or articles referrenced for why we made the given design choice? If so link them here!

* https://github.com/cosmos/interchain-security/pull/890 was a SPIKE that inspired the ideas in this document.
