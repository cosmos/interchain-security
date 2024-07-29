# CHANGELOG

## v5.1.1

*July 26, 2024*

### API BREAKING

- [Provider](x/ccv/provider)
  - Fix incorrect message defitions in the proto files of the provider module
    ([\#2095](https://github.com/cosmos/interchain-security/pull/2095))

### STATE BREAKING

- [Provider](x/ccv/provider)
  - Fix incorrect message defitions in the proto files of the provider module
    ([\#2095](https://github.com/cosmos/interchain-security/pull/2095))

## v5.1.0

*July 19, 2024*

### API BREAKING

- General
  - Remove soft opt-out feature. ([\#1995](https://github.com/cosmos/interchain-security/pull/1995))
    Backporting of ([\#1964](https://github.com/cosmos/interchain-security/pull/1964)).
- [Provider](x/ccv/provider)
  - Change the UX in key assignment by returning an error if a validator tries to
    reuse the same consumer key.
    ([\#1998](https://github.com/cosmos/interchain-security/pull/1998))

### DEPENDENCIES

- Bump [CometBFT](https://github.com/cometbft/cometbft) to
  [v0.38.9](https://github.com/cometbft/cometbft/releases/tag/v0.38.9).
  ([\#2013](https://github.com/cosmos/interchain-security/pull/2013))
- Bump [ibc-go](https://github.com/cosmos/ibc-go) to
  [v8.3.2](https://github.com/cosmos/ibc-go/releases/tag/v8.3.2).
  ([\#2053](https://github.com/cosmos/interchain-security/pull/2053))
- Bump [cosmos-sdk](https://github.com/cosmos/cosmos-sdk) to
[v0.50.8](https://github.com/cosmos/cosmos-sdk/releases/tag/v0.50.8)
([\#2053](https://github.com/cosmos/interchain-security/pull/2053))

### FEATURES

- Remove soft opt-out feature. ([\#1995](https://github.com/cosmos/interchain-security/pull/1995))
  Backporting of ([\#1964](https://github.com/cosmos/interchain-security/pull/1964)).

### STATE BREAKING

- General
  - Remove soft opt-out feature. ([\#1995](https://github.com/cosmos/interchain-security/pull/1995))
    Backporting of ([\#1964](https://github.com/cosmos/interchain-security/pull/1964)).
  - Bump [CometBFT](https://github.com/cometbft/cometbft) to
    [v0.38.9](https://github.com/cometbft/cometbft/releases/tag/v0.38.9).
    ([\#2013](https://github.com/cosmos/interchain-security/pull/2013))
  - Bump [ibc-go](https://github.com/cosmos/ibc-go) to
    [v8.3.2](https://github.com/cosmos/ibc-go/releases/tag/v8.3.2).
    ([\#2053](https://github.com/cosmos/interchain-security/pull/2053))
  - Bump [cosmos-sdk](https://github.com/cosmos/cosmos-sdk) to
    [v0.50.8](https://github.com/cosmos/cosmos-sdk/releases/tag/v0.50.8)
    ([\#2053](https://github.com/cosmos/interchain-security/pull/2053))
- [Provider](x/ccv/provider)
  - Change the UX in key assignment by returning an error if a validator tries to
    reuse the same consumer key.
    ([\#1998](https://github.com/cosmos/interchain-security/pull/1998))

## Previous Versions

[CHANGELOG of previous versions](https://github.com/cosmos/interchain-security/blob/main/CHANGELOG.md)

