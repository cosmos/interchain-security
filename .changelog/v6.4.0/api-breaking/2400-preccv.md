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