# CHANGELOG

## v4.3.0

*June 20, 2024*

### BUG FIXES

- General
  - Write unbonding period advisory to stderr instead of stdout
    ([\#1921](https://github.com/cosmos/interchain-security/pull/1921))
- [Provider](x/ccv/provider)
  - Apply audit suggestions that include a bug fix in the way we compute the
    maximum capped power.
    ([\#1925](https://github.com/cosmos/interchain-security/pull/1925))
  - Replace `GetAllConsumerChains` with lightweight version
    (`GetAllRegisteredConsumerChainIDs`) that doesn't call into the staking module
    ([\#1946](https://github.com/cosmos/interchain-security/pull/1946))

### DEPENDENCIES

- Bump [ibc-go](https://github.com/cosmos/ibc-go) to
  [v7.6.0](https://github.com/cosmos/ibc-go/releases/tag/v7.6.0).
  ([\#1974](https://github.com/cosmos/interchain-security/pull/1974))

### FEATURES

- [Provider](x/ccv/provider)
  - Allow consumer chains to change their PSS parameters.
    ([\#1932](https://github.com/cosmos/interchain-security/pull/1932))

### IMPROVEMENTS

- [Provider](x/ccv/provider)
  - Only start distributing rewards to validators after they have been validating
    for a fixed number of blocks. Introduces the `NumberOfEpochsToStartReceivingRewards` param.
    ([\#1929](https://github.com/cosmos/interchain-security/pull/1929))

### STATE BREAKING

- General
  - Bump [ibc-go](https://github.com/cosmos/ibc-go) to
    [v7.6.0](https://github.com/cosmos/ibc-go/releases/tag/v7.6.0).
    ([\#1974](https://github.com/cosmos/interchain-security/pull/1974))
- [Provider](x/ccv/provider)
  - Apply audit suggestions that include a bug fix in the way we compute the
    maximum capped power. ([\#1925](https://github.com/cosmos/interchain-security/pull/1925))
  - Only start distributing rewards to validators after they have been validating
    for a fixed number of blocks. Introduces the `NumberOfEpochsToStartReceivingRewards` param.
    ([\#1929](https://github.com/cosmos/interchain-security/pull/1929))
  - Allow consumer chains to change their PSS parameters.
    ([\#1932](https://github.com/cosmos/interchain-security/pull/1932))

## Previous Versions

[CHANGELOG of previous versions](https://github.com/cosmos/interchain-security/blob/main/CHANGELOG.md)

