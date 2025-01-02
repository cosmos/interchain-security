# Releases

- [Releases](#releases)
  - [Semantic Versioning](#semantic-versioning)
    - [Breaking Changes](#breaking-changes)
  - [Release Cycle](#release-cycle)
  - [Stable Release Policy](#stable-release-policy)
  - [Version Matrix](#version-matrix)
    - [Backwards Compatibility](#backwards-compatibility)
      - [Notes](#notes)

## Semantic Versioning

Interchain Security (ICS) follows [semantic versioning](https://semver.org), but with the following deviations (similar to [IBC-Go](https://github.com/cosmos/ibc-go/blob/main/RELEASES.md)):

- A library API breaking change will result in an increase of the MAJOR version number (X.y.z | X > 0).
- A state-machine breaking change will result in an increase of the MINOR version number (x.Y.z | x > 0).
- Any other changes (including node API breaking changes) will result in an increase of the PATCH version number (x.y.Z | x > 0).

### Breaking Changes

A change is considered to be ***library API breaking*** if it modifies the integration of ICS on either consumer or provider chains (i.e., it changes the way ICS is used as a library).
Note that bumping the major version of [Cosmos SDK](https://github.com/cosmos/cosmos-sdk) or [IBC](https://github.com/cosmos/ibc-go) will be considered as a library API breaking change.

A change is considered to be ***state-machine breaking*** if it requires a coordinated upgrade and/or state migration for either consumer or provider chains in order to preserve [state compatibility](./STATE-COMPATIBILITY.md).
Note that when bumping the dependencies of [Cosmos SDK](https://github.com/cosmos/cosmos-sdk) and [IBC](https://github.com/cosmos/ibc-go) we will only treat patch releases as non state-machine breaking.

A change is considered to be ***node API breaking*** if it modifies the API provided by a node of either consumer or provider chains.
This includes events, queries, CLI interfaces.

## Release Cycle

ICS follows a traditional release cycle involving release candidates (RCs) releases before finalizing a new version.
The stable release guarantees do not go into effect until a final release is performed.

❗***It is never advisable to use a non-final release in production.***

Final releases should contain little to no changes in comparison to the latest RC.

A release should not be finalized until the development team and the external community have done sufficient integration tests on the targeted release.

## Stable Release Policy

The beginning of a new major release series is marked by the release of a new major version.
A major release series is comprised of all minor and patch releases made under the same major version number.
The series continues to receive bug fixes (released as minor or patch releases) until it reaches end of life.
The date when a major release series reaches end of life is determined by one of the following methods:

- If there is no known chain using a major release series, then it reached end of life.
  This is a temporary policy that is possible due to the relatively low number of consumer chains.
- If the next major release is made within the first 6 months, then the end of
  life date of the major release series is 1 year after its initial release.
- If the next major release is made 6 months after the initial release, then the
  end of life date of the major release series is 6 months after the release date
  of the next major release.

Only the following major release series have a stable release status.
All missing minor release versions have been discontinued.

| Release  | End of Life Date |
| -------- | ---------------- |
| `v4.0.x` | January 24, 2025 |
| `v4.4.x` | January 24, 2025 |
| `v4.5.x` | January 24, 2025 |
| `v5.0.x` | May 9, 2025      |
| `v5.2.x` | May 9, 2025      |
| `v6.1.x` | Sep 13, 2025     |
| `v6.3.x` | Sep 13, 2025     |
| `v6.4.x` | Sep 13, 2025     |

## Version Matrix

Versions of Golang, IBC, Cosmos SDK and CometBFT used by ICS in the currently active releases:

| ICS                                                                         | Golang | IBC    | Cosmos SDK | CometBFT | Note |
| --------------------------------------------------------------------------- | ------ | ------ | ---------- | -------- | ---- |
| [v4.0.0](https://github.com/cosmos/interchain-security/releases/tag/v4.0.0) | 1.21   | v7.3.1 | v0.47.7    | v0.37.4  |      |
| [v4.4.0](https://github.com/cosmos/interchain-security/releases/tag/v4.4.0) | 1.21   | v7.6.0 | v0.47.12   | v0.37.6  |      |
| [v4.5.0](https://github.com/cosmos/interchain-security/releases/tag/v4.4.0) | 1.21   | v7.6.0 | v0.47.12   | v0.37.6  |      |
| [v5.0.0](https://github.com/cosmos/interchain-security/releases/tag/v5.0.0) | 1.21   | v8.1.0 | v0.50.4    | v0.38.5  |      |
| [v5.2.0](https://github.com/cosmos/interchain-security/releases/tag/v5.2.0) | 1.22   | v8.3.2 | v0.50.8    | v0.38.9  |      |
| [v6.1.0](https://github.com/cosmos/interchain-security/releases/tag/v6.1.0) | 1.22   | v8.5.0 | v0.50.9    | v0.38.11 |      |
| [v6.3.0](https://github.com/cosmos/interchain-security/releases/tag/v6.3.0) | 1.22   | v8.5.1 | v0.50.9    | v0.38.11 |      |
| [v6.4.0](https://github.com/cosmos/interchain-security/releases/tag/v6.4.0) | 1.22   | v8.5.2 | v0.50.11   | v0.38.15 |      |

**Note:** For a list of major ICS features available in the currently active releases, see [FEATURES.md](./FEATURES.md).

### Backwards Compatibility

A MAJOR version of ICS will always be backwards compatible with the previous MAJOR version of ICS.

The following table indicates the compatibility of currently active releases:

| Consumer            | Provider | `v5.2.0` | `v6.1.0` | `v6.3.0` | `v6.4.0` |
| ------------------- | -------- | -------- | -------- | -------- | -------- |
| `v4.0.0`            |          | ✅       | ✅       | ✅ (1)   | ✅ (1)   |
| `v4.4.0`            |          | ✅       | ✅       | ✅ (1)   | ✅ (1)   |
| `v4.5.0`            |          | ✅       | ✅       | ✅       | ✅ (1)   |
| `v5.0.0`            |          | ✅       | ✅       | ✅ (1)   | ✅ (1)   |
| `v5.2.0`            |          | ✅       | ✅       | ✅ (1)   | ✅ (1)   |
| `v6.2.0` / `v6.3.0` |          | ✅       | ✅       | ✅       | ✅ (1)   |
| `v6.4.0`            |          | ✅       | ✅       | ✅       | ✅       |

#### Notes
The following adjustments must be made to the CCV consumer genesis state that is obtained from the provider chain after the spawn time is reached in order for the consumer chain to start without errors.

- (1) Use `interchain-security-cd genesis transform` to transform the consumer genesis file obtained from the provider.