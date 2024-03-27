# CHANGELOG

## v4.1.0

<!--
*March 27, 2024*
     -->

### DEPENDENCIES

- Bump [cosmos-sdk](https://github.com/cosmos/cosmos-sdk) to
  [v0.47.10](https://github.com/cosmos/cosmos-sdk/releases/tag/v0.47.10).
  ([\#1663](https://github.com/cosmos/interchain-security/pull/1663))

### FEATURES

- [Provider](x/ccv/provider)
  - Introduce epochs (i.e., send a VSCPacket every X blocks instead of in every
    block) so that we reduce the cost of relaying IBC packets needed for ICS.
    ([\#1516](https://github.com/cosmos/interchain-security/pull/1516))

### IMPROVEMENTS

- [Provider](x/ccv/provider)
  - Added query for current values of all provider parameters
    ([\#1605](https://github.com/cosmos/interchain-security/pull/1605))

### STATE BREAKING

- [Provider](x/ccv/provider)
  - Introduce epochs (i.e., send a VSCPacket every X blocks instead of in every
    block) so that we reduce the cost of relaying IBC packets needed for ICS.
    ([\#1516](https://github.com/cosmos/interchain-security/pull/1516))

## Previous Versions

[CHANGELOG of previous versions](https://github.com/cosmos/interchain-security/blob/main/CHANGELOG.md)

