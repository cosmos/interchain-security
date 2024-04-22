# CHANGELOG

## v4.1.1

*April 22, 2024*

### BUG FIXES

- [Provider](x/ccv/provider)
  - Fix the output format of QueryAllPairsValConAddrByConsumerChainID to be consumer addresses instead of bytes
    ([\#1722](https://github.com/cosmos/interchain-security/pull/1722))

## v4.1.0

*April 17, 2024*

### DEPENDENCIES

- Bump [cosmos-sdk](https://github.com/cosmos/cosmos-sdk) to
  [v0.47.10](https://github.com/cosmos/cosmos-sdk/releases/tag/v0.47.10).
  ([\#1663](https://github.com/cosmos/interchain-security/pull/1663))
- Bump [ibc-go](https://github.com/cosmos/ibc-go) to
  [v7.4.0](https://github.com/cosmos/ibc-go/releases/tag/v7.4.0).
  ([\#1764](https://github.com/cosmos/interchain-security/pull/1764))

### FEATURES

- [Provider](x/ccv/provider)
  - Introduce epochs (i.e., send a VSCPacket every X blocks instead of in every
    block) so that we reduce the cost of relaying IBC packets needed for ICS.
    ([\#1516](https://github.com/cosmos/interchain-security/pull/1516))
  - Introduce the gRPC query `/interchain_security/ccv/provider/oldest_unconfirmed_vsc/{chain_id}`
    and CLI command `interchain-security-pd q provider oldest_unconfirmed_vsc`
    to retrieve the send timestamp of the oldest unconfirmed VSCPacket by chain id.
    ([\#1740](https://github.com/cosmos/interchain-security/pull/1740))

### IMPROVEMENTS

- [Provider](x/ccv/provider)
  - Added query for current values of all provider parameters
    ([\#1605](https://github.com/cosmos/interchain-security/pull/1605))

### STATE BREAKING

- General
  - Bump [ibc-go](https://github.com/cosmos/ibc-go) to
    [v7.4.0](https://github.com/cosmos/ibc-go/releases/tag/v7.4.0).
    ([\#1764](https://github.com/cosmos/interchain-security/pull/1764))
- [Provider](x/ccv/provider)
  - Introduce epochs (i.e., send a VSCPacket every X blocks instead of in every
    block) so that we reduce the cost of relaying IBC packets needed for ICS.
    ([\#1516](https://github.com/cosmos/interchain-security/pull/1516))

## Previous Versions

[CHANGELOG of previous versions](https://github.com/cosmos/interchain-security/blob/main/CHANGELOG.md)

