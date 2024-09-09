- Add the  Permissionless ICS feature on the provider (as per 
  [ADR-019](https://cosmos.github.io/interchain-security/adrs/adr-019-permissionless-ics)),
  which entails the following api-breaking changes on the provider.
  ([\#2171](https://github.com/cosmos/interchain-security/pull/2171))
  
  - Deprecate the `chain-id` parameter in favour of `consumer-id` for all transactions and queries targeting a unique consumer chain. Below is a list highlighting the changes in the CLI commands. All commands assume the prefix `interchain-security-pd tx|q provider`.
    - **Transactions:**
      - `assign-consensus-key [consumer-id] [consumer-pubkey]`
        -- submit a [MsgAssignConsensusKey](https://github.com/cosmos/interchain-security/blob/a17a3851b5eb3cec515b711dceae0afe9c14c3f0/proto/interchain_security/ccv/provider/v1/tx.proto#L46)
      - `opt-in [consumer-id] [consumer-pubkey]`
        -- submit a [MsgOptIn](https://github.com/cosmos/interchain-security/blob/a17a3851b5eb3cec515b711dceae0afe9c14c3f0/proto/interchain_security/ccv/provider/v1/tx.proto#L256)
      - `opt-out [consumer-id]`
        -- submit a [MsgOptOut](https://github.com/cosmos/interchain-security/blob/a17a3851b5eb3cec515b711dceae0afe9c14c3f0/proto/interchain_security/ccv/provider/v1/tx.proto#L277)
      - `set-consumer-commission-rate [consumer-id] [commission-rate]`
        -- submit a [MsgSetConsumerCommissionRate](https://github.com/cosmos/interchain-security/blob/a17a3851b5eb3cec515b711dceae0afe9c14c3f0/proto/interchain_security/ccv/provider/v1/tx.proto#L295)

    - **Queries:**
      - `consumer-genesis [consumer-id]` -- query for consumer chain genesis state by consumer id.
        - REST:`/interchain_security/ccv/provider/consumer_genesis/{consumer_id}`

      - `validator-consumer-key [consumer-id] [provider-validator-address]` -- query assigned validator consensus public key for a consumer chain.
        - REST: `/interchain_security/ccv/provider/validator_consumer_addr/{consumer_id}/{provider_address}`

      - `validator-provider-key [consumer-id] [consumer-validator-address]` -- query assigned validator consensus public key for the provider chain.
        - REST: `/interchain_security/ccv/provider/validator_provider_addr/{consumer_id}/{consumer_address}`

      - `consumer-opted-in-validators [consumer-id]` -- query opted-in validators for a given consumer chain.
        - REST: `/interchain_security/ccv/provider/opted_in_validators/{consumer_id}`

      - `consumer-validators [consumer-id]` -- query the last set consumer-validator set for a given consumer chain.
        - REST: `/interchain_security/ccv/provider/consumer_validators/{consumer_id}`

      - `validator-consumer-commission-rate [consumer-id]` -- query the consumer commission rate a validator charges on a consumer chain.
        - REST: `/interchain_security/ccv/provider/consumer_commission_rate/{consumer_id}/{provider_address}`

      - `all-pairs-valconsensus-address [consumer-id]` -- query all pairs of valconsensus address by consumer id.
        - REST: `/interchain_security/ccv/provider/address_pairs/{consumer_id}`

  - Deprecate the following queries and all the legacy governance proposals:
    - **Queries:**
      - `list-start-proposals` -- query consumer chains start proposals on provider chain.
        - REST: `/interchain_security/ccv/provider/consumer_chain_start_proposals`

      - `list-stop-proposals` -- consumer chains stop proposals on provider chain.
        - REST: `/interchain_security/ccv/provider/consumer_chain_stop_proposals`

      - `list-proposed-consumer-chains` -- query chain ids in consumer addition proposal before voting finishes.
        - REST: `/interchain_security/ccv/provider/proposed_consumer_chains`

    - **Proposals:**
      - [ConsumerAdditionProposal](https://github.com/cosmos/interchain-security/blob/a17a3851b5eb3cec515b711dceae0afe9c14c3f0/proto/interchain_security/ccv/provider/v1/provider.proto#L31)
      - [ConsumerModificationProposal](https://github.com/cosmos/interchain-security/blob/a17a3851b5eb3cec515b711dceae0afe9c14c3f0/proto/interchain_security/ccv/provider/v1/provider.proto#L140)
      - [ConsumerRemovalProposal](https://github.com/cosmos/interchain-security/blob/a17a3851b5eb3cec515b711dceae0afe9c14c3f0/proto/interchain_security/ccv/provider/v1/provider.proto#L122)
      - [ChangeRewardDenomsProposal](https://github.com/cosmos/interchain-security/blob/a17a3851b5eb3cec515b711dceae0afe9c14c3f0/proto/interchain_security/ccv/provider/v1/provider.proto#L192)  
