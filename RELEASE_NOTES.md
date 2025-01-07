# Interchain Security v6.4.0 Release Notes

## 📝 Changelog

Check out the [changelog](https://github.com/cosmos/interchain-security/blob/v6.4.0/CHANGELOG.md) for a list of relevant changes or [compare all changes](https://github.com/cosmos/interchain-security/compare/v6.3.0...v6.4.0) from last release.

Refer to the [upgrading guide](https://github.com/cosmos/interchain-security/blob/release/v6.4.x/UPGRADING.md) when migrating from `v6.3.x` to `v6.4.x`.

## 🚀 Highlights

<!-- Add any highlights of this release -->

This is a major ICS release that brings a series of improvements to both provider and consumer chains. 

- Remove the `VSCMaturedPackets` from the consumer module (as per [ADR 018](https://cosmos.github.io/interchain-security/adrs/adr-018-remove-vscmatured#consumer-changes-r2)). 
- Add a priority list to the power shaping parameters. 
- Remove the governance proposal whitelisting from consumer chains. 
- Enable the chain ID of a consumer chain to be updated after creation, but before launch. 
- Enable querying the provider module for the genesis time for a consumer chain. 
- Enable consumer chains to have customizable slashing and jailing (as per [ADR 020](https://cosmos.github.io/interchain-security/adrs/adr-020-cutomizable_slashing_and_jailing)). 
- Simplify the changeover from standalone to consumer chains by reusing the existing IBC connection to the provider.

In addition to the above improvements, this release also adds [interchain tests](https://github.com/strangelove-ventures/interchaintest) to ICS. This is an effort to simplify the testing framework and increase the confidence of ICS releases.
