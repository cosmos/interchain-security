# Interchain Security v6.2.0  Release Notes

## 📝 Changelog

Check out the [changelog](https://github.com/cosmos/interchain-security/blob/v6.2.0/CHANGELOG.md) for a list of relevant changes or [compare all changes](https://github.com/cosmos/interchain-security/compare/v6.1.0...v6.2.0) from last release.

Refer to the [upgrading guide](https://github.com/cosmos/interchain-security/blob/release/v6.2.x/UPGRADING.md) when migrating from `v6.1.x` to `v6.2.x`.

## 🚀 Highlights

<!-- Add any highlights of this release -->

This release introduces the following features:

- Populate the memo on the IBC transfer packets used to send ICS rewards.
with the required consumer chain Id to identify the consumer to the provider, see [#2290](https://github.com/cosmos/interchain-security/pull/2290).

- Enable permissionless allowlisting of reward denoms (at most 3) per consumer chain, see [#2309](https://github.com/cosmos/interchain-security/pull/2309) for more details.

In addition, it bumps the following dependencies:

- IBC-Go to [v8.5.1](https://github.com/cosmos/ibc-go/releases/tag/v8.5.0)