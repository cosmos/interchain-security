# CHANGELOG

## v4.5.0

*September 30, 2024*

### BUG FIXES

- Remove duplicate event emission on cached context.
  ([\#2282](https://github.com/cosmos/interchain-security/pull/2282))

### FEATURES

- `[x/consumer]` Populate the memo on the IBC transfer packets used to send ICS rewards.
with the required consumer chain Id to identify the consumer to the provider.
- `[x/provider]` Identify the source of ICS rewards from the IBC transfer packet memo.
  ([\#2290](https://github.com/cosmos/interchain-security/pull/2290))

### STATE BREAKING

- `[x/consumer]` Populate the memo on the IBC transfer packets used to send ICS rewards.
with the required consumer chain Id to identify the consumer to the provider.
- `[x/provider]` Identify the source of ICS rewards from the IBC transfer packet memo.
  ([\#2290](https://github.com/cosmos/interchain-security/pull/2290))

## v4.4.0

*July 16, 2024*

### API BREAKING

- Remove soft opt-out feature. 
  ([\#1964](https://github.com/cosmos/interchain-security/pull/1964))

### FEATURES

- Remove soft opt-out feature. 
  ([\#1964](https://github.com/cosmos/interchain-security/pull/1964))

### STATE BREAKING

- Remove soft opt-out feature. 
  ([\#1964](https://github.com/cosmos/interchain-security/pull/1964))

  ## Previous Versions

    [CHANGELOG of previous versions](https://github.com/cosmos/interchain-security/blob/main/CHANGELOG.md)

