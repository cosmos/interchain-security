- The removal of `VSCMaturedPackets` entail several API breaking changes.
  ([\#2098](https://github.com/cosmos/interchain-security/pull/2098))
  
  - Remove the `oldest_unconfirmed_vsc` query -- used to get
  the send timestamp of the oldest unconfirmed VSCPacket.
  - Deprecate the `init_timeout_period` and `vsc_timeout_period` parameters 
  from the provider module. 
