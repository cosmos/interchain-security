# Replicated Security v4.0.0 Release Notes

## 📝 Changelog
Check out the [changelog](https://github.com/cosmos/interchain-security/blob/v4.0.0/CHANGELOG.md) for a list of relevant changes or [compare all changes](https://github.com/cosmos/interchain-security/compare/v3.3.0...v4.0.0) from last release.

<!-- Add the following line for major releases -->
Refer to the [upgrading guide](https://github.com/cosmos/interchain-security/blob/release/v4.0.x/UPGRADING.md) when migrating 
from a version `>= v3.1.x` to `v4.0.x`.

## 🚀 Highlights

This release introduces the following noteworthy changes:

- It sets the minimum required version of Go to `1.21`.
- It adds the provider-side changes for jail throttling with retries and, as a result, it fully enables the jail throttling with retries feature (cf. [ADR 008](https://github.com/cosmos/interchain-security/blob/release/v3.2.x/docs/docs/adrs/adr-008-throttle-retries.md)).
- Fixes a bug in the soft opt-out protocol -- it avoids jailing validators immediately once they can no longer opt-out from validating consumer chains.

