# CHANGELOG

## v4.0.0

*January 22, 2024*

### API BREAKING

- [Consumer](x/ccv/consumer)
  - Fix a bug in consmer genesis file transform CLI command.
    ([\#1458](https://github.com/cosmos/interchain-security/pull/1458))

### BUG FIXES

- General
  - Fix a bug in consmer genesis file transform CLI command.
    ([\#1458](https://github.com/cosmos/interchain-security/pull/1458))
  - Improve validation of IBC packet data and provider messages. Also,
    enable the provider to validate consumer packets before handling them.
    ([\#1460](https://github.com/cosmos/interchain-security/pull/1460))
- [Consumer](x/ccv/consumer)
  - Avoid jailing validators immediately once they can no longer opt-out from
    validating consumer chains.
    ([\#1549](https://github.com/cosmos/interchain-security/pull/1549))
  - Fix the validation of VSCPackets to not fail due to marshaling to string using Bech32.
    ([\#1570](https://github.com/cosmos/interchain-security/pull/1570))

### DEPENDENCIES

- Bump Golang to v1.21 
  ([\#1557](https://github.com/cosmos/interchain-security/pull/1557))
- Bump [cosmos-sdk](https://github.com/cosmos/cosmos-sdk) to
  [v0.47.7](https://github.com/cosmos/cosmos-sdk/releases/tag/v0.47.7).
  ([\#1558](https://github.com/cosmos/interchain-security/pull/1558))
- Bump [CometBFT](https://github.com/cometbft/cometbft) to
  [v0.37.4](https://github.com/cometbft/cometbft/releases/tag/v0.37.4).
  ([\#1558](https://github.com/cosmos/interchain-security/pull/1558))

### FEATURES

- [Provider](x/ccv/provider)
  - Add the provider-side changes for jail throttling with retries (cf. ADR 008).
    ([\#1321](https://github.com/cosmos/interchain-security/pull/1321))

### STATE BREAKING

- [Consumer](x/ccv/consumer)
  - Avoid jailing validators immediately once they can no longer opt-out from
    validating consumer chains.
    ([\#1549](https://github.com/cosmos/interchain-security/pull/1549))
  - Fix the validation of VSCPackets to not fail due to marshaling to string using Bech32.
    ([\#1570](https://github.com/cosmos/interchain-security/pull/1570))
- [Provider](x/ccv/provider)
  - Add the provider-side changes for jail throttling with retries (cf. ADR 008).
    ([\#1321](https://github.com/cosmos/interchain-security/pull/1321))

## v3.3.0

*January 11, 2024*

### API BREAKING

- [Consumer](x/ccv/consumer)
  - Fix a bug in consmer genesis file transform CLI command.
    ([\#1458](https://github.com/cosmos/interchain-security/pull/1458))

### BUG FIXES

- General
  - Fix a bug in consmer genesis file transform CLI command.
    ([\#1458](https://github.com/cosmos/interchain-security/pull/1458))
  - Improve validation of IBC packet data and provider messages. Also,
    enable the provider to validate consumer packets before handling them.
    ([\#1460](https://github.com/cosmos/interchain-security/pull/1460))
- [Consumer](x/ccv/consumer)
  - Avoid jailing validators immediately once they can no longer opt-out from
    validating consumer chains.
    ([\#1549](https://github.com/cosmos/interchain-security/pull/1549))

### DEPENDENCIES

- Bump Golang to v1.21 
  ([\#1557](https://github.com/cosmos/interchain-security/pull/1557))
- Bump [cosmos-sdk](https://github.com/cosmos/cosmos-sdk) to
  [v0.47.7](https://github.com/cosmos/cosmos-sdk/releases/tag/v0.47.7).
  ([\#1558](https://github.com/cosmos/interchain-security/pull/1558))
- Bump [CometBFT](https://github.com/cometbft/cometbft) to
  [v0.37.4](https://github.com/cometbft/cometbft/releases/tag/v0.37.4).
  ([\#1558](https://github.com/cosmos/interchain-security/pull/1558))

### FEATURES

- [Provider](x/ccv/provider)
  - Add the provider-side changes for jail throttling with retries (cf. ADR 008).
    ([\#1321](https://github.com/cosmos/interchain-security/pull/1321))

### STATE BREAKING

- [Consumer](x/ccv/consumer)
  - Avoid jailing validators immediately once they can no longer opt-out from
    validating consumer chains.
    ([\#1549](https://github.com/cosmos/interchain-security/pull/1549))
- [Provider](x/ccv/provider)
  - Add the provider-side changes for jail throttling with retries (cf. ADR 008).
    ([\#1321](https://github.com/cosmos/interchain-security/pull/1321))

## Previous Versions

[CHANGELOG of previous versions](https://github.com/cosmos/interchain-security/blob/main/CHANGELOG.md)

