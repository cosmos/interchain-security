# CHANGELOG

## v6.0.0

*September 12, 2024*

### API BREAKING

- `[x/provider]` Add the  Permissionless ICS feature on the provider (as per 
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

  - Deprecate the following queries, proposals and all legacy governance proposals:

    - **Queries:**
      - `list-start-proposals` -- query consumer chains start proposals on provider chain.
        - REST: `/interchain_security/ccv/provider/consumer_chain_start_proposals`

      - `list-stop-proposals` -- consumer chains stop proposals on provider chain.
        - REST: `/interchain_security/ccv/provider/consumer_chain_stop_proposals`

      - `list-proposed-consumer-chains` -- query chain ids in consumer addition proposal before voting finishes.
        - REST: `/interchain_security/ccv/provider/proposed_consumer_chains`

    - **Proposals:**
      - [MsgConsumerAddition](https://github.com/cosmos/interchain-security/blob/a17a3851b5eb3cec515b711dceae0afe9c14c3f0/proto/interchain_security/ccv/provider/v1/tx.proto#L121) -- deprecated in favor of [MsgCreateConsumer](https://github.com/cosmos/interchain-security/blob/a17a3851b5eb3cec515b711dceae0afe9c14c3f0/proto/interchain_security/ccv/provider/v1/tx.proto#L360)
      - [MsgConsumerRemoval](https://github.com/cosmos/interchain-security/blob/a17a3851b5eb3cec515b711dceae0afe9c14c3f0/proto/interchain_security/ccv/provider/v1/tx.proto#L206) -- deprecated in favor of [MsgRemoveConsumer](https://github.com/cosmos/interchain-security/blob/a17a3851b5eb3cec515b711dceae0afe9c14c3f0/proto/interchain_security/ccv/provider/v1/tx.proto#L225)
      - [MsgConsumerModification](https://github.com/cosmos/interchain-security/blob/a17a3851b5eb3cec515b711dceae0afe9c14c3f0/proto/interchain_security/ccv/provider/v1/tx.proto#L321) -- deprecated in favor of [MsgUpdateConsumer](https://github.com/cosmos/interchain-security/blob/a17a3851b5eb3cec515b711dceae0afe9c14c3f0/proto/interchain_security/ccv/provider/v1/tx.proto#L383)
    
    - **Legacy Proposals:**
      - [ConsumerAdditionProposal](https://github.com/cosmos/interchain-security/blob/a17a3851b5eb3cec515b711dceae0afe9c14c3f0/proto/interchain_security/ccv/provider/v1/provider.proto#L31)
      - [ConsumerModificationProposal](https://github.com/cosmos/interchain-security/blob/a17a3851b5eb3cec515b711dceae0afe9c14c3f0/proto/interchain_security/ccv/provider/v1/provider.proto#L140)
      - [ConsumerRemovalProposal](https://github.com/cosmos/interchain-security/blob/a17a3851b5eb3cec515b711dceae0afe9c14c3f0/proto/interchain_security/ccv/provider/v1/provider.proto#L122)
      - [ChangeRewardDenomsProposal](https://github.com/cosmos/interchain-security/blob/a17a3851b5eb3cec515b711dceae0afe9c14c3f0/proto/interchain_security/ccv/provider/v1/provider.proto#L192)  
- `[x/provider]` Add the _Inactive Provider Validators_ feature (as per 
  [ADR-017](https://cosmos.github.io/interchain-security/adrs/adr-017-allowing-inactive-validators)),
  which entails the following changes on the provider.
  ([\#2079](https://github.com/cosmos/interchain-security/pull/2079))

  - Add `max_provider_consensus_validators`, a provider module param that sets 
    the maximum number of validators that will be passed to the provider consensus engine.
  - Add `no_valupdates_genutil` and `no_valupdates_staking`, "wrapper" modules around 
    the Cosmos SDK's native genutil and staking modules. Both modules provide the exact 
    same functionality as the native modules, except for *not* returning validator set updates 
    to the provider consensus engine.
  - Return the first `max_provider_consensus_validators` validators (sorted by largest amount of stake first)
    to the provider consensus engine. 
  - Use the `max_validators` validators as basis for the validator sets sent to the consumers 
    (`max_validators` is a staking module param).
- `[x/provider]` The removal of `VSCMaturedPackets` entail several API breaking changes.
  ([\#2098](https://github.com/cosmos/interchain-security/pull/2098))
  
  - Remove the `oldest_unconfirmed_vsc` query -- used to get
  the send timestamp of the oldest unconfirmed VSCPacket.
  - Deprecate the `init_timeout_period` and `vsc_timeout_period` parameters 
  from the provider module. 

### DEPENDENCIES

- Bump [CometBFT](https://github.com/cometbft/cometbft) to
  [v0.38.11](https://github.com/cometbft/cometbft/releases/tag/v0.38.11).
  ([\#2200](https://github.com/cosmos/interchain-security/pull/2200))
- Bump [cosmos-sdk](https://github.com/cosmos/cosmos-sdk) to
[v0.50.9](https://github.com/cosmos/cosmos-sdk/releases/tag/v0.50.9)
([\#2200](https://github.com/cosmos/interchain-security/pull/2200))
- Bump [ibc-go](https://github.com/cosmos/ibc-go) to
  [v8.5.0](https://github.com/cosmos/ibc-go/releases/tag/v8.5.0).
  ([\#2200](https://github.com/cosmos/interchain-security/pull/2200))

### FEATURES

- `[x/provider]` Add `allow_inactive_vals`, a power shaping configuration parameter that enables consumers 
  to specify whether validators outside the active provider validator set are eligible to opt-in. 
  ([\#2066](https://github.com/cosmos/interchain-security/pull/2066))
- `[x/provider]` Add `min_stake`, a power shaping configuration parameter that enables consumers to set 
  the minimum amount of provider stake every validator needs to be eligible to opt-in.
  ([\#2035](https://github.com/cosmos/interchain-security/pull/2035))
- `[x/provider]` Add a query to get the blocks until the next epoch begins
  ([\#2106](https://github.com/cosmos/interchain-security/pull/2106))
- `[x/provider]` Add the _Inactive Provider Validators_ feature (as per 
  [ADR-017](https://cosmos.github.io/interchain-security/adrs/adr-017-allowing-inactive-validators)),
  which entails the following changes on the provider.
  ([\#2079](https://github.com/cosmos/interchain-security/pull/2079))

  - Add `max_provider_consensus_validators`, a provider module param that sets 
    the maximum number of validators that will be passed to the provider consensus engine.
  - Add `no_valupdates_genutil` and `no_valupdates_staking`, "wrapper" modules around 
    the Cosmos SDK's native genutil and staking modules. Both modules provide the exact 
    same functionality as the native modules, except for *not* returning validator set updates 
    to the provider consensus engine.
  - Return the first `max_provider_consensus_validators` validators (sorted by largest amount of stake first)
    to the provider consensus engine. 
  - Use the `max_validators` validators as basis for the validator sets sent to the consumers 
    (`max_validators` is a staking module param).
- `[x/provider]` Add the _Permissionless ICS_ feature (as per 
  [ADR-019](https://cosmos.github.io/interchain-security/adrs/adr-019-permissionless-ics)),
  which entails the following CLI and API enhancements on the provider.
  ([\#2171](https://github.com/cosmos/interchain-security/pull/2171))

  - Introduce new CLI commands and gRPC endpoints to manage consumer chains. All commands listed below assume the prefix `interchain-security-pd tx|q provider`.

    - **Transactions:**
      - `create-consumer [consumer-parameters]`
        -- submit a [MsgCreateConsumer](https://github.com/cosmos/interchain-security/blob/a17a3851b5eb3cec515b711dceae0afe9c14c3f0/proto/interchain_security/ccv/provider/v1/tx.proto#L360)
        -- replace [ConsumerAdditionProposal](https://github.com/cosmos/interchain-security/blob/a17a3851b5eb3cec515b711dceae0afe9c14c3f0/proto/interchain_security/ccv/provider/v1/provider.proto#L31)

      - `update-consumer [consumer-parameters]`
        -- submit a [MsgUpdateConsumer](https://github.com/cosmos/interchain-security/blob/a17a3851b5eb3cec515b711dceae0afe9c14c3f0/proto/interchain_security/ccv/provider/v1/tx.proto#L383)
        -- replace [ConsumerModificationProposal](https://github.com/cosmos/interchain-security/blob/a17a3851b5eb3cec515b711dceae0afe9c14c3f0/proto/interchain_security/ccv/provider/v1/provider.proto#L140)

      - `remove-consumer [consumer-id]`
        -- submit a [MsgRemoveConsumer](https://github.com/cosmos/interchain-security/blob/a17a3851b5eb3cec515b711dceae0afe9c14c3f0/proto/interchain_security/ccv/provider/v1/tx.proto#L225)
        -- replace [ConsumerRemovalProposal](https://github.com/cosmos/interchain-security/blob/a17a3851b5eb3cec515b711dceae0afe9c14c3f0/proto/interchain_security/ccv/provider/v1/provider.proto#L122)

      > These new TX commands should be used instead of their corresponding deprecated proposals. To update consumer chains owned by the  governance module, a proposal containing a `MsgUpdateConsumer` message must be submitted.

    - **Queries:**
      - `consumer-chain [consumer-id]`-- query details of a consumer chain associated with the consumer id.
        - REST: `interchain-security/ccv/provider/consumer_chain/{consumer_id}`
      - `consumer-id-from-client-id [client-id]` -- get the consumer id of a chain from a client id.
        - REST: `interchain-security/ccv/provider/consumer_id/{client_id}`
      - `blocks-until-next-epoch` -- query number of blocks remaining until the next epoch begins.
        - REST: `interchain-security/ccv/provider/blocks_until_next_epoch`

  - Improve the `list-consumer-chains` query to accept optional parameters `[phase]` and `[limit]`:
    - `[phase]`: Filters returned consumer chains by their phase.
    - `[limit]`: Limits the number of consumer chains returned.
- `[x/provider]` Remove `VSCMaturedPackets` from the provider module, which entails the following 
  changes to the provider. 
  ([\#2098](https://github.com/cosmos/interchain-security/pull/2098))

  - Remove unbonding operations pausing. 
  - Remove the CCV channel initialization timeout.
  - Remove `VSCPackets` timeout.
  - Redesign key assignment pruning -- prune old consumer keys after the unbonding period elapses.
- `[x/provider]` Remove provider migrations to consensus versions lower than 7.
  To migrate the provider module from consensus version 3, 4, or 5 to consensus version 7 or higher, 
  users should use v4.3.x in production to migrate to consensus version 6.
  ([\#2211](https://github.com/cosmos/interchain-security/pull/2211))

### STATE BREAKING

- `[x/provider]` Add `allow_inactive_vals`, a power shaping configuration parameter that enables consumers 
  to specify whether validators outside the active provider validator set are eligible to opt-in. 
  ([\#2066](https://github.com/cosmos/interchain-security/pull/2066))
- `[x/provider]` Add `min_stake`, a power shaping configuration parameter that enables consumers to set 
  the minimum amount of provider stake every validator needs to be eligible to opt-in.
  ([\#2035](https://github.com/cosmos/interchain-security/pull/2035))
- `[x/provider]` Add the _Inactive Provider Validators_ feature (as per 
  [ADR-017](https://cosmos.github.io/interchain-security/adrs/adr-017-allowing-inactive-validators)).
  ([\#2079](https://github.com/cosmos/interchain-security/pull/2079))
- `[x/provider]` Add the _Permissionless ICS_ feature (as per 
  [ADR-019](https://cosmos.github.io/interchain-security/adrs/adr-019-permissionless-ics)).
  ([\#2171](https://github.com/cosmos/interchain-security/pull/2171))
- `[x/provider]` Remove `VSCMaturedPackets` from the provider module (as per 
  [ADR-018](https://cosmos.github.io/interchain-security/adrs/adr-018-remove-vscmatured)).
  ([\#2098](https://github.com/cosmos/interchain-security/pull/2098))

## Previous Versions

[CHANGELOG of previous versions](https://github.com/cosmos/interchain-security/blob/main/CHANGELOG.md)

