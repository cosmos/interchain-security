# CHANGELOG

## v6.3.0

*October 18, 2024*

### BUG FIXES

- `[x/provider]` Add check for zero rewards to the rewards distribution logic.
  ([\#2363](https://github.com/cosmos/interchain-security/pull/2363))

### IMPROVEMENTS

- `[x/provider]` Add validation for initial height and set
  default values for consumer initialization params.
  ([\#2357](https://github.com/cosmos/interchain-security/pull/2357))

### STATE BREAKING

- `[x/provider]` Add check for zero rewards to the rewards distribution logic.
  ([\#2363](https://github.com/cosmos/interchain-security/pull/2363))
- `[x/provider]` Add validation for initial height and set
  default values for consumer initialization params.
  ([\#2357](https://github.com/cosmos/interchain-security/pull/2357))

## v6.2.0

*October 4, 2024*

### DEPENDENCIES

- Bump [ibc-go](https://github.com/cosmos/ibc-go) to
  [v8.5.1](https://github.com/cosmos/ibc-go/releases/tag/v8.5.1).
  ([\#2277](https://github.com/cosmos/interchain-security/pull/2277))

### FEATURES

- `[x/consumer]` Populate the memo on the IBC transfer packets used to send ICS rewards.
with the required consumer chain Id to identify the consumer to the provider.
- `[x/provider]` Identify the source of ICS rewards from the IBC transfer packet memo.
  ([\#2290](https://github.com/cosmos/interchain-security/pull/2290))
- `[x/provider]` Enable permissionless allowlisting of reward denoms (at most 3) per consumer chain. 
  ([\#2309](https://github.com/cosmos/interchain-security/pull/2309))

### STATE BREAKING

- `[x/consumer]` Populate the memo on the IBC transfer packets used to send ICS rewards.
with the required consumer chain Id to identify the consumer to the provider.
- `[x/provider]` Identify the source of ICS rewards from the IBC transfer packet memo.
  ([\#2290](https://github.com/cosmos/interchain-security/pull/2290))
- `[x/provider]` Enable permissionless allowlisting of reward denoms (at most 3) per consumer chain.
  ([\#2309](https://github.com/cosmos/interchain-security/pull/2309))

## v6.1.0

*September 20, 2024*

### BUG FIXES

- Remove duplicate event emission on cached context.
  ([\#2282](https://github.com/cosmos/interchain-security/pull/2282))
- `[x/provider]` Add patch to enable ICS rewards from Stride to be distributed.
  ([\#2288](https://github.com/cosmos/interchain-security/pull/2288))

### STATE BREAKING

- `[x/provider]` Add patch to enable ICS rewards from Stride to be distributed.
  ([\#2288](https://github.com/cosmos/interchain-security/pull/2288))

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

## v5.2.0

*September 4, 2024*

### BUG FIXES

- `[x/provider]` Improve provider message validation.
  ([1dd3885](https://github.com/cosmos/interchain-security/commit/1dd38851dbb9e0d98c61bd11375ee7e140527833))

### STATE BREAKING

- `[x/provider]` Improve provider message validation.
  ([1dd3885](https://github.com/cosmos/interchain-security/commit/1dd38851dbb9e0d98c61bd11375ee7e140527833))

## v5.1.1

*July 26, 2024*

### API BREAKING

- `[x/provider]` Fix incorrect message definitions in the proto files of the provider module
  ([\#2095](https://github.com/cosmos/interchain-security/pull/2095))

### STATE BREAKING

- `[x/provider]` Fix incorrect message definitions in the proto files of the provider module
  ([\#2095](https://github.com/cosmos/interchain-security/pull/2095))

## v5.1.0

*July 19, 2024*

### API BREAKING

- Remove soft opt-out feature. ([\#1995](https://github.com/cosmos/interchain-security/pull/1995))
Backporting of ([\#1964](https://github.com/cosmos/interchain-security/pull/1964)).
- `[x/provider]` Change the UX in key assignment by returning an error if a validator tries to
  reuse the same consumer key.
  ([\#1998](https://github.com/cosmos/interchain-security/pull/1998))

### DEPENDENCIES

- Bump [CometBFT](https://github.com/cometbft/cometbft) to
  [v0.38.9](https://github.com/cometbft/cometbft/releases/tag/v0.38.9).
  ([\#2013](https://github.com/cosmos/interchain-security/pull/2013))
- Bump [cosmos-sdk](https://github.com/cosmos/cosmos-sdk) to
[v0.50.8](https://github.com/cosmos/cosmos-sdk/releases/tag/v0.50.8)
([\#2053](https://github.com/cosmos/interchain-security/pull/2053))
- Bump [ibc-go](https://github.com/cosmos/ibc-go) to
  [v8.3.2](https://github.com/cosmos/ibc-go/releases/tag/v8.3.2).
  ([\#2053](https://github.com/cosmos/interchain-security/pull/2053))

### FEATURES

- Remove soft opt-out feature. ([\#1995](https://github.com/cosmos/interchain-security/pull/1995))
  - Backporting of ([\#1964](https://github.com/cosmos/interchain-security/pull/1964)).

### STATE BREAKING

- Bump [CometBFT](https://github.com/cometbft/cometbft) to
  [v0.38.9](https://github.com/cometbft/cometbft/releases/tag/v0.38.9).
  ([\#2013](https://github.com/cosmos/interchain-security/pull/2013))
- Bump [cosmos-sdk](https://github.com/cosmos/cosmos-sdk) to
[v0.50.8](https://github.com/cosmos/cosmos-sdk/releases/tag/v0.50.8)
([\#2053](https://github.com/cosmos/interchain-security/pull/2053))
- Bump [ibc-go](https://github.com/cosmos/ibc-go) to
  [v8.3.2](https://github.com/cosmos/ibc-go/releases/tag/v8.3.2).
  ([\#2053](https://github.com/cosmos/interchain-security/pull/2053))
- Remove soft opt-out feature. ([\#1995](https://github.com/cosmos/interchain-security/pull/1995))
  - Backporting of ([\#1964](https://github.com/cosmos/interchain-security/pull/1964)).
- `[x/provider]` Change the UX in key assignment by returning an error if a validator tries to
  reuse the same consumer key.
  ([\#1998](https://github.com/cosmos/interchain-security/pull/1998))

## v5.0.0

*May 9, 2024*

### DEPENDENCIES

- Bump [CometBFT](https://github.com/cometbft/cometbft) to
  [v0.38.4\5](https://github.com/cometbft/cometbft/releases/tag/v0.38.5).
  ([\#1698](https://github.com/cosmos/interchain-security/pull/1698))
- Bump [cosmos-sdk](https://github.com/cosmos/cosmos-sdk) to
[v0.50.x](https://github.com/cosmos/cosmos-sdk/releases/tag/v0.50.4)
([\#1698](https://github.com/cosmos/interchain-security/pull/1698))
- Bump [ibc-go](https://github.com/cosmos/ibc-go) to
  [v8.1.x](https://github.com/cosmos/ibc-go/releases/tag/v8.1.0).
  ([\#1698](https://github.com/cosmos/interchain-security/pull/1698))

### FEATURES

- `[x/consumer]` Add consumer `MsgUpdateParams` from [cosmos-sdk](https://github.com/cosmos/cosmos-sdk).
([\#1814](https://github.com/cosmos/interchain-security/pull/1814)).
- `[x/provider]` Add provider `MsgUpdateParams` from [cosmos-sdk](https://github.com/cosmos/cosmos-sdk).
([\#1698](https://github.com/cosmos/interchain-security/pull/1698)).

### STATE BREAKING

- Bump [CometBFT](https://github.com/cometbft/cometbft) to
  [v0.38.4\5](https://github.com/cometbft/cometbft/releases/tag/v0.38.5).
  ([\#1698](https://github.com/cosmos/interchain-security/pull/1698))
- Bump [cosmos-sdk](https://github.com/cosmos/cosmos-sdk) to
[v0.50.x](https://github.com/cosmos/cosmos-sdk/releases/tag/v0.50.4)
([\#1698](https://github.com/cosmos/interchain-security/pull/1698))
- Bump [ibc-go](https://github.com/cosmos/ibc-go) to
  [v8.1.x](https://github.com/cosmos/ibc-go/releases/tag/v8.1.0).
  ([\#1698](https://github.com/cosmos/interchain-security/pull/1698))
- Revert `PutUnbondingOnHold` behavior to ICS@v1
([\#1819](https://github.com/cosmos/interchain-security/pull/1819))

## v4.5.0

*September 30, 2024*

### BUG FIXES

- Remove duplicate event emission on cached context.
  ([\#2282](https://github.com/cosmos/interchain-security/pull/2282))

### FEATURES

- `[x/consumer]` Populate the memo on the IBC transfer packets used to send ICS rewards
with the required consumer chain Id to identify the consumer to the provider.
- `[x/provider]` Identify the source of ICS rewards from the IBC transfer packet memo.
  ([\#2290](https://github.com/cosmos/interchain-security/pull/2290))

### STATE BREAKING

- `[x/consumer]` Populate the memo on the IBC transfer packets used to send ICS rewards
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

## v4.3.1

*July 4, 2024*

### BUG FIXES

- [Provider](x/ccv/provider)
  - Add missing check for the minimum height of evidence in the consumer double-vote handler.
    [#2007](https://github.com/cosmos/interchain-security/pull/2007)

### STATE BREAKING

- [Provider](x/ccv/provider)
  - Add missing check for the minimum height of evidence in the consumer double-vote handler.
    [#2007](https://github.com/cosmos/interchain-security/pull/2007)

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

## v4.2.0

May 17, 2024

### API BREAKING

- [Provider](x/ccv/provider)
  - Assigning a key that is already assigned by the same validator will now be a no-op instead of throwing an error.
    ([\#1732](https://github.com/cosmos/interchain-security/pull/1732))
  - Changes the `list-consumer-chains` query to include a `min_power_in_top_N` field, as well as fields for all power shaping parameters of the consumer.
    ([\#1863](https://github.com/cosmos/interchain-security/pull/1863))

### DEPENDENCIES

- Bump [CometBFT](https://github.com/cometbft/cometbft) to
  [v0.37.6](https://github.com/cometbft/cometbft/releases/tag/v0.37.6).
  ([\#1876](https://github.com/cosmos/interchain-security/pull/1876))
- Bump [cosmos-sdk](https://github.com/cosmos/cosmos-sdk) to
  [v0.47.11](https://github.com/cosmos/cosmos-sdk/releases/tag/v0.47.11).
  ([\#1876](https://github.com/cosmos/interchain-security/pull/1876))

### FEATURES

- [Provider](x/ccv/provider)
  - Enable Opt In and Top N chains through gov proposals.
    ([\#1587](https://github.com/cosmos/interchain-security/pull/1587))
  - Adding the Partial Set Security (PSS) feature cf. [ADR 015](https://cosmos.github.io/interchain-security/adrs/adr-015-partial-set-security).
    PSS enables consumer chains to join ICS as _Top N_ or _Opt In_ chains and enables validators to opt to validate the consumer chains they want.
    ([\#1809](https://github.com/cosmos/interchain-security/pull/1809))
  - Introduce power-shaping features for consumer chains. The features: (i) allow us to cap the total number of validators that can validate the consumer chain, (ii) set a cap on the maximum voting power (percentage-wise) a validator can have on a consumer chain, and (iii) introduce allowlist and denylists to restrict which validators are allowed or not to validate a consumer chain.
    ([\#1830](https://github.com/cosmos/interchain-security/pull/1830))
  - Changes the `list-consumer-chains` query to include a `min_power_in_top_N` field, as well as fields for all power shaping parameters of the consumer.
    ([\#1863](https://github.com/cosmos/interchain-security/pull/1863))
  - Introduces the `consumer-validators` query to retrieve the latest set consumer-validator set for a consumer chain.
    ([\#1863](https://github.com/cosmos/interchain-security/pull/1867))

### STATE BREAKING

- [Provider](x/ccv/provider)
  - Enable Opt In and Top N chains through gov proposals.
    ([\#1587](https://github.com/cosmos/interchain-security/pull/1587))
  - Assigning a key that is already assigned by the same validator will now be a no-op instead of throwing an error.
    ([\#1732](https://github.com/cosmos/interchain-security/pull/1732))
  - Adding the Partial Set Security feature cf. [ADR 015](https://cosmos.github.io/interchain-security/adrs/adr-015-partial-set-security).
    ([\#1809](https://github.com/cosmos/interchain-security/pull/1809))
  - Introduce power-shaping features for consumer chains. The features: (i) allow us to cap the total number of validators that can validate the consumer chain, (ii) set a cap on the maximum voting power (percentage-wise) a validator can have on a consumer chain, and (iii) introduce allowlist and denylists to restrict which validators are allowed or not to validate a consumer chain.
    ([\#1830](https://github.com/cosmos/interchain-security/pull/1830))

## v4.1.1

*April 22, 2024*

### BUG FIXES

- [Provider](x/ccv/provider)
  - Fix the output format of QueryAllPairsValConAddrByConsumerChainID to be consumer addresses instead of bytes
    ([\#1722](https://github.com/cosmos/interchain-security/pull/1722))

## v4.1.0

*April 17, 2024*

### DEPENDENCIES

- Bump [cosmos-sdk](https://github.com/cosmos/cosmos-sdk) to
  [v0.47.10](https://github.com/cosmos/cosmos-sdk/releases/tag/v0.47.10).
  ([\#1663](https://github.com/cosmos/interchain-security/pull/1663))
- Bump [ibc-go](https://github.com/cosmos/ibc-go) to
  [v7.4.0](https://github.com/cosmos/ibc-go/releases/tag/v7.4.0).
  ([\#1764](https://github.com/cosmos/interchain-security/pull/1764))

### FEATURES

- [Provider](x/ccv/provider)
  - Introduce epochs (i.e., send a VSCPacket every X blocks instead of in every
    block) so that we reduce the cost of relaying IBC packets needed for ICS.
    ([\#1516](https://github.com/cosmos/interchain-security/pull/1516))
  - Introduce the gRPC query `/interchain_security/ccv/provider/oldest_unconfirmed_vsc/{chain_id}`
    and CLI command `interchain-security-pd q provider oldest_unconfirmed_vsc`
    to retrieve the send timestamp of the oldest unconfirmed VSCPacket by chain id.
    ([\#1740](https://github.com/cosmos/interchain-security/pull/1740))

### IMPROVEMENTS

- [Provider](x/ccv/provider)
  - Added query for current values of all provider parameters
    ([\#1605](https://github.com/cosmos/interchain-security/pull/1605))

### STATE BREAKING

- General
  - Bump [ibc-go](https://github.com/cosmos/ibc-go) to
    [v7.4.0](https://github.com/cosmos/ibc-go/releases/tag/v7.4.0).
    ([\#1764](https://github.com/cosmos/interchain-security/pull/1764))
- [Provider](x/ccv/provider)
  - Introduce epochs (i.e., send a VSCPacket every X blocks instead of in every
    block) so that we reduce the cost of relaying IBC packets needed for ICS.
    ([\#1516](https://github.com/cosmos/interchain-security/pull/1516))

## v4.0.0

*January 22, 2024*

### API BREAKING

- [Consumer](x/ccv/consumer)
  - Fix a bug in consmer genesis file transform CLI command.
    ([\#1458](https://github.com/cosmos/interchain-security/pull/1458))

### BUG FIXES

- General
  - Fix a bug in consmer genesis file transform CLI command.
    ([\#1458](https://github.com/cosmos/interchain-security/pull/1458))
  - Improve validation of IBC packet data and provider messages. Also,
    enable the provider to validate consumer packets before handling them.
    ([\#1460](https://github.com/cosmos/interchain-security/pull/1460))
- [Consumer](x/ccv/consumer)
  - Avoid jailing validators immediately once they can no longer opt-out from
    validating consumer chains.
    ([\#1549](https://github.com/cosmos/interchain-security/pull/1549))
  - Fix the validation of VSCPackets to not fail due to marshaling to string using Bech32.
    ([\#1570](https://github.com/cosmos/interchain-security/pull/1570))

### DEPENDENCIES

- Bump Golang to v1.21 
  ([\#1557](https://github.com/cosmos/interchain-security/pull/1557))
- Bump [cosmos-sdk](https://github.com/cosmos/cosmos-sdk) to
  [v0.47.7](https://github.com/cosmos/cosmos-sdk/releases/tag/v0.47.7).
  ([\#1558](https://github.com/cosmos/interchain-security/pull/1558))
- Bump [CometBFT](https://github.com/cometbft/cometbft) to
  [v0.37.4](https://github.com/cometbft/cometbft/releases/tag/v0.37.4).
  ([\#1558](https://github.com/cosmos/interchain-security/pull/1558))

### FEATURES

- [Provider](x/ccv/provider)
  - Add the provider-side changes for jail throttling with retries (cf. ADR 008).
    ([\#1321](https://github.com/cosmos/interchain-security/pull/1321))

### STATE BREAKING

- [Consumer](x/ccv/consumer)
  - Avoid jailing validators immediately once they can no longer opt-out from
    validating consumer chains.
    ([\#1549](https://github.com/cosmos/interchain-security/pull/1549))
  - Fix the validation of VSCPackets to not fail due to marshaling to string using Bech32.
    ([\#1570](https://github.com/cosmos/interchain-security/pull/1570))
- [Provider](x/ccv/provider)
  - Add the provider-side changes for jail throttling with retries (cf. ADR 008).
    ([\#1321](https://github.com/cosmos/interchain-security/pull/1321))

## v3.3.0

*January 5, 2024*

### API BREAKING

- [Provider](x/ccv/provider)
  - Deprecate equivocation proposals.
    ([\#1340](https://github.com/cosmos/interchain-security/pull/1340))

### DEPENDENCIES

- Bump [ibc-go](https://github.com/cosmos/ibc-go) to
  [v7.3.1](https://github.com/cosmos/ibc-go/releases/tag/v7.3.1).
  ([\#1373](https://github.com/cosmos/interchain-security/pull/1373))

### FEATURES

- General
  - Add Quint model of Replicated Security.
    ([\#1336](https://github.com/cosmos/interchain-security/pull/1336))
- [Provider](x/ccv/provider)
  - Update how consumer-assigned keys are checked when a validator is
    created on the provider.
    ([\#1339](https://github.com/cosmos/interchain-security/pull/1339))
  - Introduce the cryptographic verification of equivocation feature to the provider
    (cf. [ADR-005](docs/docs/adrs/adr-005-cryptographic-equivocation-verification.md)
    & [ADR-013](docs/docs/adrs/adr-013-equivocation-slashing.md)).
    ([\#1340](https://github.com/cosmos/interchain-security/pull/1340))

### IMPROVEMENTS

- General
  - Split out consumer genesis state to reduce shared data between provider and
    consumer. ([\#1324](https://github.com/cosmos/interchain-security/pull/1324))
    - Note: This breaks json format used by augmenting Genesis files of consumer
      chains with consumer genesis content exported from provider chain. Consumer
      Genesis content exported from a provider chain using major version 1, 2 or 3
      of the provider module needs to be transformed with the transformation command
      introduced by this PR:
      ```
      Transform the consumer genesis file from a provider version v1, v2 or v3 to a version supported by this consumer. Result is printed to STDOUT.
      
      Example:
      $ <appd> transform /path/to/ccv_consumer_genesis.json
      
      Usage:
      interchain-security-cd genesis transform [genesis-file] [flags]
      ```
  - Refactor shared events, codecs and errors assign to
    consumer and provider dedicated types where possible.
    ([\#1350](https://github.com/cosmos/interchain-security/pull/1350))
- [Provider](x/ccv/provider)
  - Add `QueryAllPairsValConAddrByConsumerChainID` method to get list of all pairs `valConsensus` address by `Consummer chainID`. ([\#1503](https://github.com/cosmos/interchain-security/pull/1503))

### STATE BREAKING

- General
  - Split out consumer genesis state to reduce shared data between provider and
    consumer. ([\#1324](https://github.com/cosmos/interchain-security/pull/1324))
  - Improve validation of IBC packet data and provider messages. Also,
    enable the provider to validate consumer packets before handling them.
    ([\#1460](https://github.com/cosmos/interchain-security/pull/1460))
- [Provider](x/ccv/provider)
  - Change the states by adding a consumer key for each chain that is
    not yet registered meaning for which the gov proposal has not passed.
    ([\#1339](https://github.com/cosmos/interchain-security/pull/1339))
  - Introduce the cryptographic verification of equivocation feature to the provider
    (cf. [ADR-005](docs/docs/adrs/adr-005-cryptographic-equivocation-verification.md)
    & [ADR-013](docs/docs/adrs/adr-013-equivocation-slashing.md)).
    ([\#1340](https://github.com/cosmos/interchain-security/pull/1340))

## v3.2.0

*November 24, 2023*

### BUG FIXES

- [Consumer](x/ccv/consumer)
  - Fix deletion of pending packets that may cause duplicate sends
    ([\#1146](https://github.com/cosmos/interchain-security/pull/1146))
  - Remove `idx` field from the `ccv.ConsumerPacketData` type as this would break the
    wire ([\#1150](https://github.com/cosmos/interchain-security/pull/1150))
  - Validate token transfer messages before calling `Transfer()`.
    ([\#1244](https://github.com/cosmos/interchain-security/pull/1244))
  - Remove incorrect address validation on `ProviderFeePoolAddrStr` param.
    ([\#1262](https://github.com/cosmos/interchain-security/pull/1262))
  - Increment consumer consensus version and register consumer migration.
    ([\#1295](https://github.com/cosmos/interchain-security/pull/1295))

### DEPENDENCIES

- Bump [ibc-go](https://github.com/cosmos/ibc-go) to
  [v7.2.0](https://github.com/cosmos/ibc-go/releases/tag/v7.2.0).
  ([\#1196](https://github.com/cosmos/interchain-security/pull/1196))
- Bump [cosmos-sdk](https://github.com/cosmos/cosmos-sdk) to
  [v0.47.4](https://github.com/cosmos/cosmos-sdk/releases/tag/v0.47.4).
  ([\#1258](https://github.com/cosmos/interchain-security/pull/1258))
- Bump [ibc-go](https://github.com/cosmos/ibc-go) to
  [v7.3.0](https://github.com/cosmos/ibc-go/releases/tag/v7.3.0).
  ([\#1258](https://github.com/cosmos/interchain-security/pull/1258))
- Bump [cosmos-sdk](https://github.com/cosmos/cosmos-sdk) to
  [v0.47.5](https://github.com/cosmos/cosmos-sdk/releases/tag/v0.47.5).
  ([\#1259](https://github.com/cosmos/interchain-security/pull/1259))

### FEATURES

- [Consumer](x/ccv/consumer)
  - Add the consumer-side changes for jail throttling with retries (cf. ADR 008).
    ([\#1024](https://github.com/cosmos/interchain-security/pull/1024))
  - Introduce the gRPC query `/interchain_security/ccv/consumer/provider-info`
    and CLI command `interchain-security-cd q ccvconsumer provider-info`
    to retrieve provider info from the consumer chain.
    ([\#1164](https://github.com/cosmos/interchain-security/pull/1164))
- [Provider](x/ccv/provider)
  - Add `InitTimeoutTimestamps` and `ExportedVscSendTimestamps` to exported
    genesis. ([\#1076](https://github.com/cosmos/interchain-security/pull/1076))
  - Add a governance proposal for setting on the provider the denominations for
    rewards from consumer chains.
    ([\#1280](https://github.com/cosmos/interchain-security/pull/1280))

### IMPROVEMENTS

- General
  - Update the default consumer unbonding period to 2 weeks.
    ([\#1244](https://github.com/cosmos/interchain-security/pull/1244))
- [Consumer](x/ccv/consumer)
  - Optimize pending packets storage on consumer, with migration.
    ([\#1037](https://github.com/cosmos/interchain-security/pull/1037))

### STATE BREAKING

- General
  - Bump [ibc-go](https://github.com/cosmos/ibc-go) to
    [v7.2.0](https://github.com/cosmos/ibc-go/releases/tag/v7.2.0).
    ([\#1196](https://github.com/cosmos/interchain-security/pull/1196))
  - Update the default consumer unbonding period to 2 weeks.
    ([\#1244](https://github.com/cosmos/interchain-security/pull/1244))
  - Bump [cosmos-sdk](https://github.com/cosmos/cosmos-sdk) to
    [v0.47.4](https://github.com/cosmos/cosmos-sdk/releases/tag/v0.47.4).
    ([\#1258](https://github.com/cosmos/interchain-security/pull/1258))
  - Bump [ibc-go](https://github.com/cosmos/ibc-go) to
    [v7.3.0](https://github.com/cosmos/ibc-go/releases/tag/v7.3.0).
    ([\#1258](https://github.com/cosmos/interchain-security/pull/1258))
  - Bump [cosmos-sdk](https://github.com/cosmos/cosmos-sdk) to
    [v0.47.5](https://github.com/cosmos/cosmos-sdk/releases/tag/v0.47.5).
    ([\#1259](https://github.com/cosmos/interchain-security/pull/1259))
- [Consumer](x/ccv/consumer)
  - Add the consumer-side changes for jail throttling with retries (cf. ADR 008).
    ([\#1024](https://github.com/cosmos/interchain-security/pull/1024))
  - Optimize pending packets storage on consumer, with migration.
    ([\#1037](https://github.com/cosmos/interchain-security/pull/1037))
  - Fix deletion of pending packets that may cause duplicate sends
    ([\#1146](https://github.com/cosmos/interchain-security/pull/1146))
  - Remove `idx` field from the `ccv.ConsumerPacketData` type as this would break the
    wire ([\#1150](https://github.com/cosmos/interchain-security/pull/1150))
  - Validate token transfer messages before calling `Transfer()`.
    ([\#1244](https://github.com/cosmos/interchain-security/pull/1244))
  - Remove incorrect address validation on `ProviderFeePoolAddrStr` param.
    ([\#1262](https://github.com/cosmos/interchain-security/pull/1262))
  - Increment consumer consensus version and register consumer migration.
    ([\#1295](https://github.com/cosmos/interchain-security/pull/1295))
- [Provider](x/ccv/provider)
  - Add a governance proposal for setting on the provider the denominations for
    rewards from consumer chains.
    ([\#1280](https://github.com/cosmos/interchain-security/pull/1280))

## v3.1.0

Date July 11th, 2023

A minor upgrade to v3.0.0, which removes the panic in the consumer ccv module which would occur in an emergency scenario where the ccv channel is closed. This release also fixes how a distribution related event is emitted, and bumps cometbft.

* (feat) [#1127](https://github.com/cosmos/interchain-security/pull/1127) Remove consumer panic when ccv channel is closed
* (fix) [#720](https://github.com/cosmos/interchain-security/issues/720) Fix the attribute `AttributeDistributionTotal` value in `FeeDistribution` event emit.
* (deps) [#1119](https://github.com/cosmos/interchain-security/pull/1119) bump cometbft from `v0.37.1` to `0.37.2`.

## v3.0.0

Date: June 21st, 2023

Interchain Security v3 uses SDK 0.47 and IBC 7.

* (fix) [#1093](https://github.com/cosmos/interchain-security/pull/1093) Make SlashPacketData backward compatible when sending data over the wire 
* (deps) [#1019](https://github.com/cosmos/interchain-security/pull/1019) Bump multiple dependencies. 
  * Bump [cosmos-sdk](https://github.com/cosmos/cosmos-sdk) to [v0.47.3](https://github.com/cosmos/cosmos-sdk/releases/tag/v0.47.3).
  * Bump [ibc-go](https://github.com/cosmos/ibc-go) to [v7.1.0](https://github.com/cosmos/ibc-go/releases/tag/v7.1.0).
  * Bump [CometBFT](https://github.com/cometbft/cometbft) to [v0.37.1](https://github.com/cometbft/cometbft/releases/tag/v0.37.1).
* `[x/ccv/provider]` (fix) [#945](https://github.com/cosmos/interchain-security/issues/945) Refactor `AfterUnbondingInitiated` to not panic when `PutUnbondingOnHold` returns error.
* `[x/ccv/provider]` (fix) [#977](https://github.com/cosmos/interchain-security/pull/977) Avoids panicking the provider when an unbonding delegation was removed through a `CancelUnbondingDelegation` message.
* `[x/ccv/democracy]` (feat) [#1019](https://github.com/cosmos/interchain-security/pull/1019) Whitelisting non-legacy params in the "democracy module" require the entire module to be whitelisted. 

## v2.4.0-lsm

*November 20, 2023*

* (fix) [#1439](https://github.com/cosmos/interchain-security/pull/1439) Fix unmarshaling for the CLI consumer double vote cmd.
* (feat!) [#1435](https://github.com/cosmos/interchain-security/pull/1435) Add height-base filter for consumer equivocation evidence.

## v2.3.0-provider-lsm

*November 15, 2023*

❗ *This release is deprecated and should not be used in production.*

* (fix!) [#1422](https://github.com/cosmos/interchain-security/pull/1422) Fix the misbehaviour handling by verifying the signatures of byzantine validators.

## v2.2.0-provider-lsm

❗ *This release is deprecated and should not be used in production.*

### Cryptographic verification of equivocation
* New feature enabling the provider chain to verify equivocation evidence on its own instead of trusting consumer chains, see [EPIC](https://github.com/cosmos/interchain-security/issues/732).

## v2.1.0-provider-lsm

Date: September 15th, 2023

* (feature!) [#1280](https://github.com/cosmos/interchain-security/pull/1280) provider proposal for changing reward denoms

## v2.0.0-lsm

Date: August 18th, 2023

* (deps!) [#1120](https://github.com/cosmos/interchain-security/pull/1120) Bump [Cosmos SDK](https://github.com/cosmos/cosmos-sdk) to [v0.45.16-ics-lsm](https://github.com/cosmos/cosmos-sdk/tree/v0.45.16-ics-lsm). This requires adapting ICS to support this SDK release. Changes are state breaking.
* (fix) [#720](https://github.com/cosmos/interchain-security/issues/720) Fix the attribute `AttributeDistributionTotal` value in `FeeDistribution` event emit.

## v2.0.0

Date: June 1st, 2023

Unlike prior releases, the ICS `v2.0.0` release will be based on the main branch. `v2.0.0` will contain all the accumulated PRs from the various releases below, along with other PRs that were merged, but not released to production. After `v2.0.0`, we plan to revamp release practices, and how we modularize the repo for consumer/provider.

Upgrading a provider from `v1.1.0-multiden` to `v2.0.0` will require state migrations. See [migration.go](https://github.com/cosmos/interchain-security/blob/v2.0.0/x/ccv/provider/keeper/migration.go).

Upgrading a consumer from `v1.2.0-multiden` to `v2.0.0` will NOT require state migrations. 

Some PRs from v2.0.0 may reappear from other releases below. This is due to the fact that ICS v1.1.0 deviates from the commit ordering of the main branch, and other releases thereafter are based on v1.1.0.

### High level changes included in v2.0.0

* MVP for standalone to consumer changeover, see [EPIC](https://github.com/cosmos/interchain-security/issues/756)
* MVP for soft opt out, see [EPIC](https://github.com/cosmos/interchain-security/issues/851)
* Various fixes, critical and non-critical
* Docs updates which should not affect production code

## Notable PRs included in v2.0.0

* (feat!) Add DistributionTransmissionChannel to ConsumerAdditionProposal [#965](https://github.com/cosmos/interchain-security/pull/965)
* (feat/fix) limit vsc matured packets handled per endblocker [#1004](https://github.com/cosmos/interchain-security/pull/1004)
* (fix) consumer key prefix order to avoid complex migrations [#963](https://github.com/cosmos/interchain-security/pull/963) and [#991](https://github.com/cosmos/interchain-security/pull/991). The latter PR is the proper fix.
* (feat) v1->v2 migrations to accommodate a bugfix having to do with store keys, introduce new params, and deal with consumer genesis state schema changes [#975](https://github.com/cosmos/interchain-security/pull/975) and [#997](https://github.com/cosmos/interchain-security/pull/997)
* (deps) Bump github.com/cosmos/ibc-go/v4 from 4.4.0 to 4.4.2 [#982](https://github.com/cosmos/interchain-security/pull/982)
* (fix) partially revert key assignment type safety PR [#980](https://github.com/cosmos/interchain-security/pull/980)
* (fix) Remove panics on failure to send IBC packets [#876](https://github.com/cosmos/interchain-security/pull/876)
* (fix) Prevent denom DOS [#931](https://github.com/cosmos/interchain-security/pull/931)
* (fix) multisig for assigning consumer key, use json [#916](https://github.com/cosmos/interchain-security/pull/916)
* (deps) Bump github.com/cosmos/ibc-go/v4 from 4.3.0 to 4.4.0 [#902](https://github.com/cosmos/interchain-security/pull/902)
* (feat) Add warnings when provider unbonding is shorter than consumer unbonding [#858](https://github.com/cosmos/interchain-security/pull/858)
* (chore) use go 1.19 [#899](https://github.com/cosmos/interchain-security/pull/899), [#840](https://github.com/cosmos/interchain-security/pull/840)
* (feat) Standalone to consumer changeover - recycle existing transfer channel [#832](https://github.com/cosmos/interchain-security/pull/832)
* (deps) Bump IBC [862](https://github.com/cosmos/interchain-security/pull/862)
* (testing) Add tests for soft opt out [#857](https://github.com/cosmos/interchain-security/pull/857)
* (feat) Standalone to consumer changeover - staking functionalities [#794](https://github.com/cosmos/interchain-security/pull/794)
* (fix) prevent provider from sending VSCPackets with multiple updates for the same validator [#850](https://github.com/cosmos/interchain-security/pull/850)
* (feat) Soft opt out [#833](https://github.com/cosmos/interchain-security/issues/833)
* (fix) Correctly handle VSC packet with duplicate val updates on consumer [#846](https://github.com/cosmos/interchain-security/pull/846)
* (deps) bump sdk to v0.45.15.ics [#805](https://github.com/cosmos/interchain-security/pull/805)
* (refactor) Remove spm module [#812](https://github.com/cosmos/interchain-security/pull/812)
* (feat) Standalone to consumer changeover part 1 [#757](https://github.com/cosmos/interchain-security/pull/757)
* (chore) Swap names of e2e and integration tests [#681](https://github.com/cosmos/interchain-security/pull/681)
* (fix) fix StopConsumerChain not running in cachedContext [#802](https://github.com/cosmos/interchain-security/pull/802). Also in earlier releases with different commit order!
* (docs) Introduce docs website [#759](https://github.com/cosmos/interchain-security/pull/759)
* (fix) Serialize correct byte prefix for SlashLogKey [#786](https://github.com/cosmos/interchain-security/pull/786)
* (feature) Improve keeper field validation [#766](https://github.com/cosmos/interchain-security/pull/766)
* (docs) Contributing guidelines [#744](https://github.com/cosmos/interchain-security/pull/744)
* (refactor) Key assignment type safety [#725](https://github.com/cosmos/interchain-security/pull/725) 
* (fix) Update protos and fix deps [#752](https://github.com/cosmos/interchain-security/pull/752)
* (api) Add consumer QueryParams [#746](https://github.com/cosmos/interchain-security/pull/746)
* (feature) New validation for keeper fields [#740](https://github.com/cosmos/interchain-security/pull/740)

## v1.2.0-multiden

The first release candidate for a fix built on top of v1.2.0, intended for consumers. This release adds a list of denoms on the consumer that are allowed to be sent to the provider as rewards. This prevents a potential DOS attack that was discovered during the audit of Replicated Security performed by Oak Security and funded by the Cosmos Hub community through Proposal 687. In an effort to move quickly, this release also includes a multisig fix that is effective only for provider. It shouldn't affect the consumer module.

Note PRs were made in a private security repo.

[full diff](https://github.com/cosmos/interchain-security/compare/v1.2.0...v1.2.0-multiden-rc0)

## v1.1.0-multiden

This release combines two fixes on top of v1.1.0, that we judged were urgent to get onto the Cosmos Hub before the launch of the first ICS consumer chain. This is an emergency release intended for providers.

The first fix is to enable the use of multisigs and Ledger devices when assigning keys for consumer chains. The second is to prevent a possible DOS vector involving the reward distribution system.

Note PRs were made in a private security repo.

[full diff](https://github.com/cosmos/interchain-security/compare/v1.1.0...release/v1.1.0-multiden)

### Multisig fix

On April 25th (a week and a half ago), we began receiving reports that validators using multisigs and Ledger devices were getting errors reading Error: unable to resolve type URL /interchain_security.ccv.provider.v1.MsgAssignConsumerKey: tx parse error when attempting to assign consensus keys for consumer chains.

We quickly narrowed the problem down to issues having to do with using the PubKey type directly in the MsgAssignConsumerKey transaction, and Amino (a deprecated serialization library still used in Ledger devices and multisigs) not being able to handle this. We attempted to fix this with the assistance of the Cosmos-SDK team, but after making no headway for a few days, we decided to simply use a JSON representation of the PubKey in the transaction. This is how it is usually represented anyway. We have verified that this fixes the problem.

### Distribution fix

The ICS distribution system works by allowing consumer chains to send rewards to a module address on the provider called the FeePoolAddress. From here they are automatically distributed to all validators and delegators through the distribution system that already exists to distribute staking rewards. The FeePoolAddress is usually blocked so that no tokens can be sent to it, but to enable ICS distribution we had to unblock it.

We recently realized that unblocking the FeePoolAddress could enable an attacker to send a huge number of different denoms into the distribution system. The distribution system would then attempt to distribute them all, leading to out of memory errors. Fixing a similar attack vector that existed in the distribution system before ICS led us to this realization.

To fix this problem, we have re-blocked the FeePoolAddress and created a new address called the ConsumerRewardsPool. Consumer chains now send rewards to this new address. There is also a new transaction type called RegisterConsumerRewardDenom. This transaction allows people to register denoms to be used as rewards from consumer chains. It costs 10 Atoms to run this transaction.The Atoms are transferred to the community pool. Only denoms registered with this command are then transferred to the FeePoolAddress and distributed out to delegators and validators.

## v1.2.1

* (fix) Remove SPM [#812](https://github.com/cosmos/interchain-security/pull/812)
* (refactor) Key assignment type safety [#725](https://github.com/cosmos/interchain-security/pull/725)

## v1.2.0

Date: April 13th, 2023

* (feat) Soft opt-out [#833](https://github.com/cosmos/interchain-security/pull/833)
* (fix) Correctly handle VSC packet with duplicate val updates on consumer [#846](https://github.com/cosmos/interchain-security/pull/846)
* (chore) bump: sdk v0.45.15-ics [#805](https://github.com/cosmos/interchain-security/pull/805)
* (api) add interchain security consumer QueryParams [#746](https://github.com/cosmos/interchain-security/pull/746)

## v1.1.1

* (fix) Remove SPM [#812](https://github.com/cosmos/interchain-security/pull/812)
* (refactor) Key assignment type safety [#725](https://github.com/cosmos/interchain-security/pull/725)

## v1.1.0

Date: March 24th, 2023

* (fix) StopConsumerChain not running in cachedContext [#802](https://github.com/cosmos/interchain-security/pull/802)

## v1.0.0

Date: February 6th, 2023

This is the first version of Interchain Security (ICS), also known as _Replicated Security_ (RS).
Replicated Security is a feature which will allow a chain -- referred to as the _provider_ -- to share security with other chains -- referred to as _consumers_.
This means that the provider's validator set will be granted the right to validate consumer chains.
The communication between the provider and the consumer chains is done through the IBC protocol over a unique, ordered channel (one for each consumer chain). Thus, RS is an IBC application.

### Features / sub-protocols

RS consist of the following core features:

- **Channel Initialization**: Enables the provider to add new consumer chains. This process is governance-gated, i.e., to add a new consumer chain, a `ConsumerAdditionProposal` governance proposal must be sent to the provider and it must receive the necessary votes.
- **Validator Set Update**: Enables the provider to 
  (1) update the consumers on the voting power granted to validators (based on the changes in the active validator set on the provider chain), 
  and (2) ensure the timely completion of unbonding operations (e.g., undelegations).
- **Consumer Initiated Slashing**: Enables the provider to jail validators for downtime infractions on the consumer chains. 
- **Reward Distribution**: Enables the consumers to transfer to the provider (over IBC) a portion of their block rewards as payment for the security provided. Once transferred, these rewards are distributed on the provider using the protocol in the [distribution module of Cosmos SDK](https://docs.cosmos.network/v0.45/modules/distribution/). 
- **Consumer Chain Removal**: Enables the provider to remove a consumer either after a `ConsumerRemovalProposal` passes governance or after one of the timeout periods elapses -- `InitTimeoutPeriod`, `VscTimeoutPeriod`, `IBCTimeoutPeriod`.
- **Social Slashing**: Equivocation offenses (double signing etc.) on consumer chains are logged, and then can be used in a governance proposal to slash the validators responsible.

In addition, RS has the following features:

- **Key Assignment**: Enables validator operators to use different consensus keys for each consumer chain validator node that they operate.
- **Jail Throttling**: Enables the provider to slow down a "worst case scenario" attack where a malicious consumer binary attempts to jail a significant amount (> 2/3) of the voting power, effectively taking control of the provider.

