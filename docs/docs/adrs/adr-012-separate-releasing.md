---
sidebar_position: 13
title: Separate Releasing
---
# ADR 012: Separate Releasing

## Changelog

* {8/18/22}: Initial draft of idea in [#801](https://github.com/cosmos/interchain-security/issues/801)
* {8/22/22}: Put idea in this ADR

## Status

Accepted

## Context

### Spike results

I explored the idea of [#801](https://github.com/cosmos/interchain-security/issues/801) with this [spike branch](https://github.com/cosmos/interchain-security/tree/shawn%2Fgo-mod-split-aug-spike). Here's my conclusions:

Splitting this repo to have multiple go.mods is possible. However there are various intricacies involved in decoupling the package hierarchy to have `x/ccv/types` as the lowest level dep, with `x/ccv/consumer` and `x/ccv/provider` being one dep layer above, with high-level tests depending on all three of the mentioned packages. I'd estimate this decoupling would take 2-5 workdays to finish, and require significant review effort.

### Why go.mod split is not the way to go

Let's take a step back and remember the issue we're trying to solve - **We need a clean way to decouple semver/releasing for the consumer and provider modules**. After more consideration, splitting up go.mods gives us little benefit in achieving this. Reasons:

* The `go.mod` dependency system is tied to git tags for the entire repo (ex: `require github.com/cometbft/cometbft v0.37.2` refers to a historical tag for the entire cometbft repo).
* It'd be an odd dev experience to allow modules to reference past releases of other modules in the same repo. When would we ever want the consumer module to reference a past release of the types module for example?
* If we allow for `go.mod` replace statements to build from local source code, why split up the package deps at all?
* Splitting go.mods adds a bunch of complexity with `go.work` files and all that shiz. VSCode does not play well with multiple module repos either.

### Why separate repos is cool but also not the way to go

All this considered, the cleanest solution to decoupling semver/releasing for the consumer and provider modules would be to have multiple repos, each with their own go.mod (3-4 repos total including high level tests). With this scheme we could separately tag each repo as changes are merged, they could share some code from `types` being an external dep, etc.

I don't think any of us want to split up the monorepo, that's a lot of work and seems like bikeshedding. There's another solution that's very simple..  

## Decision

Slightly adapting [the current semver ruleset](https://github.com/cosmos/interchain-security/blob/cca008d856e3ffc60ec1a486871d0faa702abe26/CONTRIBUTING.md#semantic-versioning):

* A library API breaking change TO EITHER MODULE will result in an increase of the MAJOR version number for both the consumer and provider modules. Most often this will involve bumping a major version of sdk or a large change to the protocol that warrants new a major version for consumer/provider anyways.  
* A state breaking change (change requiring coordinated upgrade and/or state migration) will result in an increase of the MINOR version number FOR THAT MODULE (consumer-x.Y.z or provider-x.Y.z ).
* Any other changes (including node API breaking changes) will result in an increase of the PATCH version number FOR THAT MODULE (consumer-x.y.Z or provider-x.y.Z).

For each PR merged to main (something like this should be in our PR template):

* If this PR is library API breaking, bump the go.mod version string of the repo, and the PR will result in a new major release for the consumer and provider.
* Else if this PR is state breaking to consumer, provider, or both, the PR will accordingly result in new minor release(s).
* Else if this PR has other changes, the PR will accordingly result in new patch release(s).

## Consequences

### Positive

* Consumer repos have clear communication of what tagged versions are relevant to them. Consumer devs should know to never reference an ICS version that starts with `provider`, even if it'd technically build.
* Consumer and provider modules do not deviate as long as we continually release off a shared main branch. Backporting remains relatively unchanged besides being explicit about what module(s) your changes should affect.
* No code changes, just changes in process. Very simple.

### Negative

* Slightly more complexity.
* This solution does not allow having provider and consumer on separate versions of e.g. the Cosmos SDK
### Neutral

## References

> Are there any relevant PR comments, issues that led up to this, or articles referenced for why we made the given design choice? If so link them here!

* [#801](https://github.com/cosmos/interchain-security/issues/801)
* [#801 comment](https://github.com/cosmos/interchain-security/issues/801#issuecomment-1683349298)
