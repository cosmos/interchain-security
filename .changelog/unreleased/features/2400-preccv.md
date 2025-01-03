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