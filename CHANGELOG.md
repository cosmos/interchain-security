# CHANGELOG

## v6.4.0

*January 7, 2025*

### API BREAKING

- Enable existing (standalone) chains to use the existing client (and connection)
  to the provider chain when becoming a consumer chain. This feature introduces 
  the following API-breaking changes.
  ([\#2400](https://github.com/cosmos/interchain-security/pull/2400))
  
  - Add `connection_id` and `preCCV` to `ConsumerGenesisState`, the consumer 
  genesis state created by the provider chain. If the `connection_id` is not empty,
  `preCCV` is set to true and both `provider.client_state` and `provider.consensus_state`
  are set to nil (as the consumer doesn't need to create a new provider client).
  As a result, for older versions of consumers, the `connection_id` in 
  `ConsumerInitializationParameters` must be empty and the resulting `ConsumerGenesisState`
  needs to be adapted, i.e., both `connection_id` and `preCCV` need to be removed. 

### BUG FIXES

- Bump [cosmossdk.io/math](https://github.com/cosmos/cosmos-sdk/tree/main/math) to
  [v1.4.0](https://github.com/cosmos/cosmos-sdk/tree/math/v1.4.0)
  ([\#2408](https://github.com/cosmos/gaia/pull/2408))
- `[x/consumer]` Updated `genesis transform` CLI to transform `consumer-genesis` content exported by v6.2 providers for consumer chains at version v5. Removed transformation for older consumer versions.
  ([\#2373](https://github.com/cosmos/interchain-security/pull/2373))
- `[x/provider]` Fixed pagination bug in query for listing the consumer chains.
  ([\#2398](https://github.com/cosmos/interchain-security/pull/2398))
- `[x/provider]` Fixed pagination in the list consumer chains query.
  ([\#2377](https://github.com/cosmos/interchain-security/pull/2377))

### DEPENDENCIES

- Bump [CometBFT](https://github.com/cometbft/cometbft) to
  [v0.38.15](https://github.com/cometbft/cometbft/releases/tag/v0.38.15).
  ([\#2390](https://github.com/cosmos/interchain-security/pull/2390))
- Bump [cosmos-sdk](https://github.com/cosmos/cosmos-sdk) to
  [v0.50.11](https://github.com/cosmos/cosmos-sdk/releases/tag/v0.50.11)
  ([\#2458](https://github.com/cosmos/interchain-security/pull/2458))
- Bump [cosmossdk.io/math](https://github.com/cosmos/cosmos-sdk/tree/main/math) to
  [v1.4.0](https://github.com/cosmos/cosmos-sdk/tree/math/v1.4.0)
  ([\#2408](https://github.com/cosmos/gaia/pull/2408))
- Bump [ibc-go](https://github.com/cosmos/ibc-go) to
  [v8.5.2](https://github.com/cosmos/ibc-go/releases/tag/v8.5.2).
  ([\#2390](https://github.com/cosmos/interchain-security/pull/2390))

### FEATURES

- Enable existing (standalone) chains to use the existing client (and connection)
  to the provider chain when becoming a consumer chain. This feature introduces 
  the following changes.
  ([\#2400](https://github.com/cosmos/interchain-security/pull/2400))
  
  - Add `connection_id` to `ConsumerInitializationParameters`, the ID of 
  the connection end _on the provider chain_ on top of which the CCV channel will 
  be established. Consumer chain owners can set `connection_id` to a valid ID in 
  order to reuse the underlying clients.
  - Add `connection_id` to the consumer genesis state, the ID of the connection 
  end _on the consumer chain_ on top of which the CCV channel will be established.
  If `connection_id` is a valid ID, then the consumer chain will use the underlying 
  client as the provider client and it will initiate the channel handshake.
- `[x/consumer]` Remove `VSCMaturedPackets`. Consumer-side changes for [ADR 018](https://cosmos.github.io/interchain-security/adrs/adr-018-remove-vscmatured#consumer-changes-r2).
  ([\#2372](https://github.com/cosmos/interchain-security/pull/2372))
- `[x/provider]` Add query for consumer genesis time,
 which corresponds to creation time of consumer clients.
([\#2366](https://github.com/cosmos/interchain-security/pull/2366))
- `[x/provider]` Allow consumer chains to specify a list of priority validators that are included in the validator set before other validators are considered
  ([\#2101](https://github.com/cosmos/interchain-security/pull/2101))
- `[x/provider]` Allow the chain id of a consumer chain to be updated before the chain
  launches. ([\#2378](https://github.com/cosmos/interchain-security/pull/2378))
- `[x/provider]` Enable the customization of the slashing and jailing conditions 
  for infractions committed by validators on consumer chains (as per 
  [ADR 020](https://cosmos.github.io/interchain-security/adrs/adr-020-cutomizable_slashing_and_jailing)). 
  Every consumer chain can decide the punishment for every type of infraction.
  ([\#2403](https://github.com/cosmos/interchain-security/pull/2403))
- `[x/provider]` Prevent Opt-In chains from launching, unless at least one active validator has opted-in to them.
  ([\#2101](https://github.com/cosmos/interchain-security/pull/2399))

### IMPROVEMENTS

- `[x/democracy/governance]` Removal of consumer governance whitelisting functionality
  ([\#2381](https://github.com/cosmos/interchain-security/pull/2381))

### STATE BREAKING

- Allow the chain id of a consumer chain to be updated before the chain
  launches. ([\#2378](https://github.com/cosmos/interchain-security/pull/2378))
- Bump [cosmos-sdk](https://github.com/cosmos/cosmos-sdk) to
  [v0.50.11](https://github.com/cosmos/cosmos-sdk/releases/tag/v0.50.11)
  ([\#2458](https://github.com/cosmos/interchain-security/pull/2458))
- Enable existing (standalone) chains to use the existing client (and connection)
  to the provider chain when becoming a consumer chain.
  ([\#2400](https://github.com/cosmos/interchain-security/pull/2400))
- `[x/consumer]` Remove `VSCMaturedPackets`. Consumer-side changes for [ADR 018](https://cosmos.github.io/interchain-security/adrs/adr-018-remove-vscmatured#consumer-changes-r2).
  ([\#2372](https://github.com/cosmos/interchain-security/pull/2372))
- `[x/democracy/governance]` Removal of consumer governance whitelisting functionality
  ([\#2381](https://github.com/cosmos/interchain-security/pull/2381))
- `[x/provider]` Allow consumer chains to specify a list of priority validators that are included in the validator set before other validators are considered
  ([\#2101](https://github.com/cosmos/interchain-security/pull/2101))
- `[x/provider]` Enable the customization of the slashing and jailing conditions 
  for infractions committed by validators on consumer chains (as per 
  [ADR 020](https://cosmos.github.io/interchain-security/adrs/adr-020-cutomizable_slashing_and_jailing)). 
  Every consumer chain can decide the punishment for every type of infraction.
  ([\#2403](https://github.com/cosmos/interchain-security/pull/2403))

## Previous Versions

[CHANGELOG of previous versions](https://github.com/cosmos/interchain-security/blob/main/CHANGELOG.md)

