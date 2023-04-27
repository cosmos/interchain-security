---
sidebar_position: 4
title: Separating consumer and provider libraries
---
# ADR 004: Separating consumer and provider libraries

## Changelog
* 2023-04-27: Initial draft

## Status

> A decision may be "proposed" if it hasn't been agreed upon yet, or "accepted" once it is agreed upon. If a later ADR changes or reverses a decision, it may be marked as "deprecated" or "superseded" with a reference to its replacement.

{Deprecated|Proposed|Accepted}

## Context
The main deliverable for interchain-security are consumer and provider libraries that are currently located in `x/ccv/provider` and `x/ccv/consumer`.
Any blockchain applications available in the interchain-security repository are used for testing purposes only and should be viewed as examples for building chains implementing ICS.

By cosmos-sdk terminology and conventions, all applications in the interchain-security repos are just `simapp`s:
* `interchain-security-pd` is a `simapp` for testing the provider ICS library 
* `interchain-security-cd` is a `simapp` for testing the consumer ICS library

Any apps existing in the interchain-security repository should not be considered as deliverables as they are not intended to be used by ICS customers, aside from usage in e2e testing frameworks.

Splitting consumer and provider libraries allows different release cycles and makes development easier while maintaining provider and consumer compatibility.
Versioning library code shared between the consumer and provider arises as an intermediary step in the process of splitting the provider and consumer concerns.
By versioning the shared provider and consumer code we benefit from not having to lock the provider and consumer to the same dependencies at all times.

## Handling shared functionality
At present provider and consumer libraries share some functionality, type, interfaces and constants.

Most of the shared funcionality comes from the fact that the provider chain has to communicate the initial validator set to the consumer so that the consumer can include it in its genesis.json (consumer has to know the state of the provider's validator set when the first consumer block is produced). The remainder of shared functionality comprises ICS messaging types and their validation.

It is important to notice that most of the shared types originate from .proto files. The .proto types are not versioned in `main` which means that any change to .proto types affects both consumer and provider. At present, the consumer and the provider cannot deviate from one another in any way. This is a hinderance and a bottleneck, since work on consumer and provider libraries can be paralelized by introducing a clean split between provider and consumer libraries.


### Build tooling incompatibility prevents rapid development
cosmos-sdk v0.45 and v0.47 use different build tools:
* https://docs.cosmos.network/v0.47/tooling/protobuf
* https://docs.cosmos.network/v0.47/migrations/upgrading#protobuf

`interchain-security` is only half way migrated to the tooling required for `cosmos-sdk v0.47`. Even though ICS has been upgraded to use `buf` the dependency on `gogo/protobuf` remains because `cosmos-sdk v0.45` requires it. Meanwhile, `cosmos-sdk v0.47` has migrated to use [cosmos/gogoproto](https://github.com/cosmos/gogoproto).

Besides that, ICS relies on older build tool images (ghcr.io/cosmos/proto-builder). To be compatible with `cosmos-sdk v0.47` ICS needs to upgrade the proto build image to `ghcr.io/cosmos/proto-builder >= 0.11.5`.

### Versioning shared dependencies
To enable smooth upgrade from cosmos-sdk `v0.45` to `v0.47` the proto build tooling must be upgraded. The proto build tooling cannot be upgraded incrementally, it has to be upgraded all at once.
To mitigate issues and preserve the QA for both provider and consumer the shared dependencies should be versioned (tagged).

Shared dependencies will be moved to a separate `core` module that will be built using the proto tooling intended for its corresponding `cosmos-sdk` version.

Initially, we create two `core` module tags:
* `core-45/0.1.0` -> uses legacy build tooling and `cosmos-sdk v0.45` (tag name is subject to change)
* `core-47/0.1.0` -> uses new build tooling and `cosmos-sdk v0.47` (tag name is subject to change)

With these changes we will make the shared dependencies available for cosmos-sdk `v0.45` and `v0.47`. This will allow us to add features to ICS versions that still use `cosmos-sdk v0.45` in case we need to perform emergency procedures for ICS versions `<= 1.2.x`.

Any work using `cosmos-sdk v0.47` will be uninterrupted by emergency upgrades to older versions.

### QA considerations
We rely on the QA process to assure that provider and consumer are compatible. Breaking the QA will essentially leave us in the dark for a prolonged period of time. We would be doing lots of changes without having a way to reliably ensure that we are not introducing regressions and breaking the core protocol.

Besides that, we cannot allow for `main` to be in a broken state for prolonged periods of time because an emergency release would be very difficult to execute. Since emergency releases do happen (as has been shown with dragonberry and changes in ICS regarding consumer chain removals) we cannot simply ignore the systemic risk they introduce. Our workflows must be adapted in a way that accounts for emergency scenarios, to the best of our ability.

### Future prospects
In the future, it is likely that P&C will be locked to the same dependency versions for 90% of the time. However, having the option to remain compatible while performing dependency upgrades will significantly speed up development on both sides.

Changes in build tooling without versioning the `core` module would affect both C and P which would preclude the split.

## Steps to perform
The proto build tooling has changed significantly between cosmos-sdk `v0.45` and cosmos-sdk `v0.47`. Due to the fact that `main` currently uses a legacy version of the proto build tool chain, simply upgrading the toolchain breaks both provider and consumer.

The changes to proto build system cannot go unaddressed, and they should be addressed first in order to allow smoother development of both provider and consumer.

1. separate out the `core` module that comprises types, functions and interfaces shared by provider and consumer
2. version (tag) the `core-v45` module using legacy proto build tooling (`cosmos-sdk v0.45`, `gogo/protobuf`, `ghcr.io/cosmos/proto-builder >= 0.9.0`)
3. version (tag) the `core-v47` module using latest protobuild tooling (`cosmos-sdk v0.47`, `cosmos/gogoproto`, `ghcr.io/cosmos/proto-builder >= 0.11.5`)
4. use `core-v45` in the current implementations of provider and consumer libraries
5. use `core-v47` in the future implementation provider and consumer libraries


## Decision

> This section explains all of the details of the proposed solution, including implementation details.
It should also describe affects / corollary items that may need to be changed as a part of this.
If the proposed change will be large, please also indicate a way to do the change to maximize ease of review.
(e.g. the optimal split of things to do between separate PR's)

## Consequences

> This section describes the consequences, after applying the decision. All consequences should be summarized here, not just the "positive" ones.

### Positive
TODO
### Negative
TODO

### Neutral
TODO

## References

> Are there any relevant PR comments, issues that led up to this, or articles referrenced for why we made the given design choice? If so link them here!

* {reference link}
