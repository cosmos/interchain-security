- Remove `VSCMaturedPackets` from the provider module, which entails the following 
  changes to the provider. 
  ([\#2098](https://github.com/cosmos/interchain-security/pull/2098))

  - Remove unbonding operations pausing. 
  - Remove the CCV channel initialization timeout.
  - Remove `VSCPackets` timeout.
  - Redesign key assignment pruning -- prune old consumer keys after the unbonding period elapses.
