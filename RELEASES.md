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
The stable release guarantees do not go into affect until a final release is performed.

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

| Release | End of Life Date |
|---------|------------------|
| `v2.0.x` | June 09, 2024 |
| `v2.1.x-provider-lsm` | June 09, 2024 |
| `v2.4.x-lsm` | June 09, 2024 |
| `v3.1.x` | July 10, 2024 |
| `v3.2.x` | July 10, 2024 |
| `v3.3.x` | July 10, 2024 |
| `v4.0.x` | TBA |

**Note**: As of [Gaia v12.0.0](https://github.com/cosmos/gaia/releases/tag/v12.0.0),
the Cosmos Hub uses a fork of Cosmos SDK ([v0.45.16-ics-lsm](https://github.com/cosmos/cosmos-sdk/releases/tag/v0.45.16-ics-lsm))
that contains the Liquid Staking Module (LSM).
This means the Cosmos Hub requires a fork of ICS.
This fork is maintained by the development team and released using the `-lsm` prefix.
As soon as the Cosmos Hub uses mainline Cosmos SDK, the `-lsm` releases will reach end of life.

## Version Matrix

Versions of Golang, IBC, Cosmos SDK and CometBFT used by ICS in the currently active releases:

| ICS | Golang | IBC | Cosmos SDK | CometBFT | Note |
|-----|--------|-----|------------|----------|------|
| [v2.0.0](https://github.com/cosmos/interchain-security/releases/tag/v2.0.0) | 1.19 | v4.4.2 | v0.45.15-ics | v0.34.28 |
| [v2.1.0-provider-lsm](https://github.com/cosmos/interchain-security/releases/tag/v2.1.0-provider-lsm) | 1.19 | v4.4.2 | v0.45.16-ics-lsm | v0.34.28 | Provider only (Cosmos Hub specific) |
| [v2.4.0-lsm](https://github.com/cosmos/interchain-security/releases/tag/v2.4.0-lsm) | 1.19 | v4.4.2 | v0.45.16-ics-lsm | v0.34.28 | Provider only (Cosmos Hub specific) |
| [v3.1.0](https://github.com/cosmos/interchain-security/releases/tag/v3.1.0) | 1.20 | v7.1.0 | v0.47.3 | v0.37.2 |
| v3.2.0 | 1.20 | v7.3.0 | v0.47.5 | v0.37.2 |
| v3.3.0 | 1.20 | v7.3.0 | v0.47.5 | v0.37.2 |
| v4.0.0 | 1.20 | v7.3.0 | v0.47.5 | v0.37.2 | Provider on >= v4.0.0 backwards compatible with consumers >= v3.2.0 |

**Note:** For a list of major ICS features available in the currently active releases, see [FEATURES.md](./FEATURES.md).

### Backwards Compatibility

A MAJOR version of ICS will always be backwards compatible with the previous MAJOR version of ICS.

The following table indicates the compatibility of currently active releases:

| Consumer | Provider | `v2.0.0` | `v2.1.0-provider-lsm` | `v2.4.0-lsm` | `v3.1.0` | `v3.2.0` | `v3.3.0` | `v4.0.0` |
|----------|----------|----------|-----------------------|--------------|----------|----------|----------|----------|
| `v2.0.0` || ✅ | ✅ | ✅ | ✅ (2) | ✅ (2) | ✅ (2),(3) | ❌ |
| `v3.1.0` || ✅ | ✅ | ✅ | ✅ | ✅ | ✅ (3) | ❌ |
| `v3.2.0` || ✅ | ✅ | ✅ | ✅ | ✅ | ✅ (3) | ✅ |
| `v3.3.0` || ✅ (3)| ✅ (3)| ✅ (3)| ✅ (3) | ✅ (3) | ✅ | ✅ |
| `v4.0.0` || ✅ (3) | ✅ (3) | ✅ (3) | ✅ (3) | ✅ (3)| ✅ (3)| ✅ |

#### Notes

The following adjustments must be made to the CCV consumer genesis state that is obtained from the provider chain after the spawn time is reached in order for the consumer chain to start without errors.

- (1) Remove “preCCV” key
- (2) Remove “prehash_key_before_comparison” keys
- (3) Use `interchain-security-cd genesis transform` to transform the consumer genesis file obtained from the provider.