# Replicated Security v5.1.0  Release Notes

## 📝 Changelog
Check out the [changelog](https://github.com/cosmos/interchain-security/blob/v5.1.0/CHANGELOG.md) for a list of relevant changes or [compare all changes](https://github.com/cosmos/interchain-security/compare/v4.3.1...v5.1.0) from last release.

<!-- Add the following line for major or minor releases -->
Refer to the [upgrading guide](https://github.com/cosmos/interchain-security/blob/release/v5.1.x/UPGRADING.md) when migrating from `v4.3.x` to `v5.1.x`.

## 🚀 Highlights

Cosmos SDK v0.50 upgrade:

* (deps) [\#2013](https://github.com/cosmos/interchain-security/pull/2013) Bump multiple dependencies.
  * Bump Cosmos-SDK to v0.50.8.
  * Bump IBC-Go to v8.3.2.
  * Bump CometBFT to v0.38.9.

API-breaking change:

* (feat) [\#1998](https://github.com/cosmos/interchain-security/pull/1998) Change the UX of the provider's
 [key assignment feature](docs/docs/features/key-assignment.md) to return an error if a validator
 tries to reuse the same consumer key.

* (feat) [\#1995](https://github.com/cosmos/interchain-security/pull/1995) Deprecate the
 [Soft opt-out Feature](docs/docs/adrs/adr-009-soft-opt-out.md).

