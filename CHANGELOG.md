# CHANGELOG

## v5.0.0-provider

May 1, 2024

### API BREAKING

- [Provider](x/ccv/provider)
  - Assigning a key that is already assigned by the same validator will now be a no-op instead of throwing an error.
    ([\#1732](https://github.com/cosmos/interchain-security/pull/1732))

### FEATURES

- [Provider](x/ccv/provider)
  - Enable Opt In and Top N chains through gov proposals.
    ([\#1587](https://github.com/cosmos/interchain-security/pull/1587))
  - Adding the Partial Set Security (PSS) feature cf. [ADR 015](https://cosmos.github.io/interchain-security/adrs/adr-015-partial-set-security).
    PSS enables consumer chains to join ICS as _Top N_ or _Opt In_ chains and enables validators to opt to validate the consumer chains they want.
    ([\#1809](https://github.com/cosmos/interchain-security/pull/1809))
  - Introduce power-shaping features for consumer chains. The features: (i) allow us to cap the total number of validators that can validate the consumer chain, (ii) set a cap on the maximum voting power (percentage-wise) a validator can have on a consumer chain, and (iii) introduce allowlist and denylists to restrict which validators are allowed or not to validate a consumer chain.
    ([\#1830](https://github.com/cosmos/interchain-security/pull/1830))

### STATE BREAKING

- [Provider](x/ccv/provider)
  - Enable Opt In and Top N chains through gov proposals.
    ([\#1587](https://github.com/cosmos/interchain-security/pull/1587))
  - Assigning a key that is already assigned by the same validator will now be a no-op instead of throwing an error.
    ([\#1732](https://github.com/cosmos/interchain-security/pull/1732))
  - Adding the Partial Set Security feature cf. [ADR 015](https://cosmos.github.io/interchain-security/adrs/adr-015-partial-set-security).
    ([\#1809](https://github.com/cosmos/interchain-security/pull/1809))
  - Introduce power-shaping features for consumer chains. The features: (i) allow us to cap the total number of validators that can validate the consumer chain, (ii) set a cap on the maximum voting power (percentage-wise) a validator can have on a consumer chain, and (iii) introduce allowlist and denylists to restrict which validators are allowed or not to validate a consumer chain.
    ([\#1830](https://github.com/cosmos/interchain-security/pull/1830))

## Previous Versions

    [CHANGELOG of previous versions](https://github.com/cosmos/interchain-security/blob/main/CHANGELOG.md)

