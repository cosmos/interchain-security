
- Add the  Permissionless ICS feature on the provider (as per 
  [ADR-019](https://cosmos.github.io/interchain-security/adrs/adr-019-permissionless-ics)),
  which entails the following api-breaking changes on the provider.
  ([\#2171](https://github.com/cosmos/interchain-security/pull/2171))
  
  - Deprecate the `chain-id` parameter in favour of `consumer-id` for all transactions and queries targeting a unique consumer chain. Below is a list highlighting the changes in the CLI commands. All commands assume the prefix `interchain-security-pd tx/q provider`.
    
    - **Transactions**
    | Command                                 | Message                             |
    |-----------------------------------------|-------------------------------------|
    | `assign-consensus-key [consumer-id] [consumer-pubkey]`  | [MsgAssignConsensusKey](https://github.com/cosmos/interchain-security/blob/feat/permissionless/proto/interchain_security/ccv/provider/v1/tx.proto#L256)             |
    | `opt-in [consumer-id] [consumer-pubkey]`               | [MsgOptIn](https://github.com/cosmos/interchain-security/blob/feat/permissionless/proto/interchain_security/ccv/provider/v1/tx.proto#L256)                          |
    | `opt-out [consumer-id]`                                | [MsgOptOut](https://github.com/cosmos/interchain-security/blob/feat/permissionless/proto/interchain_security/ccv/provider/v1/tx.proto#L256)                         |
    | `set-consumer-commission-rate [consumer-id] [commission-rate]` | [MsgSetConsumerCommissionRate](https://github.com/cosmos/interchain-security/blob/feat/permissionless/proto/interchain_security/ccv/provider/v1/tx.proto#L295) |


  - **Queries:**
    | Command                                        | gRPC Endpoint                                              |
    |------------------------------------------------|------------------------------------------------------------|
    | `consumer-genesis [consumer-id]`               | `/interchain_security/ccv/provider/consumer_genesis/{consumer_id}`        |
    | `validator-consumer-key [consumer-id] [provider-validator-address]` | `/interchain_security/ccv/provider/validator_consumer_addr/{consumer_id}/{provider_address}`   |
    | `validator-provider-key [consumer-id] [consumer-validator-address]` | `/interchain_security/ccv/provider/validator_provider_addr/{consumer_id}/{consumer_address}`   |
    | `consumer-opted-in-validators [consumer-id]`   | `/interchain_security/ccv/provider/opted_in_validators/{consumer_id}` |
    | `consumer-validators [consumer-id]`            | `/interchain_security/ccv/provider/consumer_validators/{consumer_id}`      |
    | `validator-consumer-commission-rate [consumer-id]` | `/interchain_security/ccv/provider/consumer_commission_rate/{consumer_id}/{provider_address}` |
    | `all-pairs-valconsensus-address [consumer-id]` | `/interchain_security/ccv/provider/address_pairs/{consumer_id}` |


- Deprecate the following queries and governance proposals:
  - **Queries:**
    | Command                                 | gRPC Endpoint                                                   |
    |-----------------------------------------|-----------------------------------------------------------------|    
    | `list-start-proposals`                   | `/interchain_security/ccv/provider/consumer_chain_start_proposals` |
    | `list-stop-proposals`                   | `/interchain_security/ccv/provider/consumer_chain_stop_proposals`  |
    | `list-proposed-consumer-chains`         | `/interchain_security/ccv/provider/proposed_consumer_chains`       |
  - **Proposals:**
    - [ConsumerAdditionProposal](https://github.com/cosmos/interchain-security/blob/feat/permissionless/proto/interchain_security/ccv/provider/v1/provider.proto#L31)
    - [ConsumerModificationProposal](https://github.com/cosmos/interchain-security/blob/feat/permissionless/proto/interchain_security/ccv/provider/v1/provider.proto#L140)
    - [ConsumerRemovalProposal](https://github.com/cosmos/interchain-security/blob/feat/permissionless/proto/interchain_security/ccv/provider/v1/provider.proto#L122)  
    
([\#2171](https://github.com/cosmos/interchain-security/pull/2171))