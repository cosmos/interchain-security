# Replicated Security v3.2.0  Release Notes

## 📝 Changelog

Check out the [changelog](https://github.com/cosmos/interchain-security/blob/v3.2.0/CHANGELOG.md) for a list of relevant changes or [compare all changes](https://github.com/cosmos/interchain-security/compare/release/v3.1.0...v3.2.0) from last release.

## 🚀 Highlights

<!-- Add any highlights of this release -->
The main highlight of this release are the consumer-side changes for jail throttling with retries (cf. [ADR 008](https://github.com/cosmos/interchain-security/blob/release/v3.2.x/docs/docs/adrs/adr-008-throttle-retries.md)). 
These changes are compatible with providers running previous versions. 
Once all consumers have deployed these changes, the provider-side changes will also be deployed to production, fully enabling jail throttling with retries. 