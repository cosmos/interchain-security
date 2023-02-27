# Contributing

- [Contributing](#contributing)
  - [Architecture Decision Records (ADR)](#architecture-decision-records-adr)
  - [PR Targeting](#pr-targeting)
  - [Development Procedure](#development-procedure)
  - [Branching Model and Release](#branching-model-and-release)
  - [Testing](#testing)
  - [Protobuf](#protobuf)

Thank you for considering making contributions to ICS!

To contribute, you could start by browsing [new issues](https://github.com/cosmos/interchain-security/issues).

## Architecture Decision Records (ADR)

When proposing an architecture decision for ICS, please start by opening an [issue](https://github.com/cosmos/interchain-security/issues/new/choose) with a summary of the proposal. Once the proposal has been discussed and there is rough alignment on a high-level approach to the design, you may either start development, or write an ADR.

If your architecture decision is a simple change, you may contribute directly without writing an ADR. However, if you are proposing a significant change, please include a corresponding ADR.

In certain circumstances, the architecture decision may require changes to the ICS spec. Note that the spec is responsible for defining language-agnostic, implementation-agnostic behaviors for the ICS protocol. Whereas ADRs are responsible for communicating implementation decisions contained within this repo.

To create an ADR, follow the [template](https://github.com/cosmos/interchain-security/blob/main/docs/architecture/adr-template.md) and [doc](https://github.com/cosmos/interchain-security/blob/main/docs/architecture/README.md). If you would like to see examples of how these are written, please refer to the current [ADRs](https://github.com/cosmos/interchain-security/tree/main/docs/architecture).

### ADR Proposals

Architecture Decision Records (ADRs) may be proposed by any contributors or maintainers of ICS. ADRs are intended to be iterative, and may be merged into `main` while still in a `Proposed` status

## PR Targeting

All feature additions and all bug fixes must be targeted against `main`. Exception is for bug fixes which are only related to a released version. In that case, the related bug fix PRs must target against the release branch.

If needed, we backport a commit from `main` to a release branch (excluding consensus breaking feature, API breaking and similar).

## Development Procedure

- The latest state of development is on `main`
- `main` must never fail `make test`
- Create a branch or fork the repo to start work
- Once development is completed, or during development as a draft, you may open a pull request. The pull request description should follow the [default template](./.github/PULL_REQUEST_TEMPLATE.md). Note that a PR can be of one or multiple types, including `Feature`, `Fix`, `Refactor`, `Testing`, and `Docs`. Please try to minimize the number of categories that you could classify a single PR as.
- It's notable that your PR may have versioning implications. See [Branching Model and Release](#branching-model-and-release) for more information
- Code is squash merged through the PR approval process.

## Branching Model and Release

ICS adheres to the [trunk based development branching model](https://trunkbaseddevelopment.com/) and a variation of [semantic versioning](https://semver.org/).

ICS is a distributed, IBC based protocol in which multiple blockchains could be affected by a version bump. Therefore incrementing a MAJOR version number indicates that the PR is a breaking change to the way that the provider and consumer(s) communicate with one another over IBC. That is, if a feature is consensus breaking to both the provider and consumer(s), then it requires a MAJOR version bump.

Incrementing a MINOR version number indicates that a PR is only consensus breaking to the provider, or only to the consumers. Be careful in this scenario, as state-transition changes to the provider can often lead to differences in how validator set changes are relayed to the consumers.

Incrementing a PATCH version number indicates that a PR is not consensus breaking to the provider or consumers.

Pure documentation, testing, and refactoring PRs do not require a version bump.

## Testing

Appropriate tests should be written with a new feature, and all existing tests should pass. See [docs/testing.md](./docs/testing.md) for more information.

## Protobuf

We use [Protocol Buffers](https://developers.google.com/protocol-buffers) along with [gogoproto](https://github.com/gogo/protobuf) to generate code for use in ICS.

For determinstic behavior around Protobuf tooling, everything is containerized using Docker. Make sure to have Docker installed on your machine, or head to [Docker's website](https://docs.docker.com/get-docker/) to install it.

To generate the protobuf stubs, you can run `make proto-gen`.
