<!-- This file is auto-generated. Please do not modify it yourself. -->
# Protobuf Documentation
<a name="top"></a>

## Table of Contents

- [interchain_security/ccv/v1/ccv.proto](#interchain_security/ccv/v1/ccv.proto)
    - [SlashPacketData](#interchain_security.ccv.v1.SlashPacketData)
    - [UnbondingOp](#interchain_security.ccv.v1.UnbondingOp)
    - [ValidatorSetChangePacketData](#interchain_security.ccv.v1.ValidatorSetChangePacketData)
  
    - [Status](#interchain_security.ccv.v1.Status)
  
- [interchain_security/ccv/consumer/v1/consumer.proto](#interchain_security/ccv/consumer/v1/consumer.proto)
    - [CrossChainValidator](#interchain_security.ccv.consumer.v1.CrossChainValidator)
    - [LastTransmissionBlockHeight](#interchain_security.ccv.consumer.v1.LastTransmissionBlockHeight)
    - [Params](#interchain_security.ccv.consumer.v1.Params)
    - [SlashRequest](#interchain_security.ccv.consumer.v1.SlashRequest)
  
- [interchain_security/ccv/consumer/v1/genesis.proto](#interchain_security/ccv/consumer/v1/genesis.proto)
    - [GenesisState](#interchain_security.ccv.consumer.v1.GenesisState)
    - [UnbondingSequence](#interchain_security.ccv.consumer.v1.UnbondingSequence)
  
- [interchain_security/ccv/provider/v1/provider.proto](#interchain_security/ccv/provider/v1/provider.proto)
    - [ConsumerAdditionProposal](#interchain_security.ccv.provider.v1.ConsumerAdditionProposal)
    - [HandshakeMetadata](#interchain_security.ccv.provider.v1.HandshakeMetadata)
    - [Params](#interchain_security.ccv.provider.v1.Params)
  
- [interchain_security/ccv/provider/v1/genesis.proto](#interchain_security/ccv/provider/v1/genesis.proto)
    - [ConsumerState](#interchain_security.ccv.provider.v1.ConsumerState)
    - [GenesisState](#interchain_security.ccv.provider.v1.GenesisState)
  
- [interchain_security/ccv/provider/v1/query.proto](#interchain_security/ccv/provider/v1/query.proto)
    - [QueryConsumerGenesisRequest](#interchain_security.ccv.provider.v1.QueryConsumerGenesisRequest)
    - [QueryConsumerGenesisResponse](#interchain_security.ccv.provider.v1.QueryConsumerGenesisResponse)
  
    - [Query](#interchain_security.ccv.provider.v1.Query)
  
- [interchain_security/ccv/v1/query.proto](#interchain_security/ccv/v1/query.proto)
    - [Query](#interchain_security.ccv.v1.Query)
  
- [interchain_security/ccv/v1/tx.proto](#interchain_security/ccv/v1/tx.proto)
    - [Msg](#interchain_security.ccv.v1.Msg)
  
- [Scalar Value Types](#scalar-value-types)



<a name="interchain_security/ccv/v1/ccv.proto"></a>
<p align="right"><a href="#top">Top</a></p>

## interchain_security/ccv/v1/ccv.proto



<a name="interchain_security.ccv.v1.SlashPacketData"></a>

### SlashPacketData
This packet is sent from the consumer chain to the provider chain.
The acknowledgement will be sent asynchrounously when the jailing 
will be started on the provider chain.


| Field | Type | Label | Description |
| ----- | ---- | ----- | ----------- |
| `validator` | [tendermint.abci.Validator](#tendermint.abci.Validator) |  |  |
| `jail_time` | [int64](#int64) |  |  |
| `slash_fraction` | [int64](#int64) |  |  |
| `valset_update_id` | [uint64](#uint64) |  |  |






<a name="interchain_security.ccv.v1.UnbondingOp"></a>

### UnbondingOp



| Field | Type | Label | Description |
| ----- | ---- | ----- | ----------- |
| `id` | [uint64](#uint64) |  |  |
| `unbonding_consumer_chains` | [string](#string) | repeated | consumer chains that are still unbonding |






<a name="interchain_security.ccv.v1.ValidatorSetChangePacketData"></a>

### ValidatorSetChangePacketData
This packet is sent from provider chain to consumer chain if the validator set for consumer chain
changes (due to new bonding/unbonding messages or slashing events)
The acknowledgement from consumer chain will be sent asynchronously once unbonding period is over,
and this will function as `UnbondingOver` message for this packet.


| Field | Type | Label | Description |
| ----- | ---- | ----- | ----------- |
| `validator_updates` | [tendermint.abci.ValidatorUpdate](#tendermint.abci.ValidatorUpdate) | repeated |  |
| `valset_update_id` | [uint64](#uint64) |  |  |
| `slash_acks` | [string](#string) | repeated | consensus address of consumer chain validators successfully slashed on the provider chain |





 <!-- end messages -->


<a name="interchain_security.ccv.v1.Status"></a>

### Status
Status defines if the ccv channel is in one of the following states:
UNINITIALIZED, INITIALIZING, VALIDATING, INVALID

| Name | Number | Description |
| ---- | ------ | ----------- |
| STATUS_UNINITIALIZED_UNSPECIFIED | 0 | Default State |
| STATUS_INITIALIZING | 1 | channel is in handshake process |
| STATUS_VALIDATING | 2 | channel is open and validating |
| STATUS_INVALID | 3 | channel is invalid and can no longer process packets |


 <!-- end enums -->

 <!-- end HasExtensions -->

 <!-- end services -->



<a name="interchain_security/ccv/consumer/v1/consumer.proto"></a>
<p align="right"><a href="#top">Top</a></p>

## interchain_security/ccv/consumer/v1/consumer.proto



<a name="interchain_security.ccv.consumer.v1.CrossChainValidator"></a>

### CrossChainValidator
CrossChainValidator defines the validators for CCV consumer module


| Field | Type | Label | Description |
| ----- | ---- | ----- | ----------- |
| `address` | [bytes](#bytes) |  |  |
| `power` | [int64](#int64) |  |  |






<a name="interchain_security.ccv.consumer.v1.LastTransmissionBlockHeight"></a>

### LastTransmissionBlockHeight
LastTransmissionBlockHeight is the last time validator holding
pools were transmitted to the provider chain


| Field | Type | Label | Description |
| ----- | ---- | ----- | ----------- |
| `Height` | [int64](#int64) |  |  |






<a name="interchain_security.ccv.consumer.v1.Params"></a>

### Params
Params defines the parameters for CCV consumer module


| Field | Type | Label | Description |
| ----- | ---- | ----- | ----------- |
| `Enabled` | [bool](#bool) |  |  |
| `BlocksPerDistributionTransmission` | [int64](#int64) |  | Distribution Params Number of blocks between ibc-token-transfers from the consumer chain to the provider chain. Note that at this transmission event a fraction of the accumulated tokens are divided and sent consumer redistribution address. |
| `DistributionTransmissionChannel` | [string](#string) |  | Channel, and provider-chain receiving address to send distribution token transfers over. These parameters is auto-set during the consumer <-> provider handshake procedure. |
| `ProviderFeePoolAddrStr` | [string](#string) |  |  |
| `ConsumerRedistributeFrac` | [string](#string) |  | The fraction of tokens allocated to the consumer redistribution address during distribution events. The fraction is a string representing a decimal number. For example "0.5" would represent 50%. |






<a name="interchain_security.ccv.consumer.v1.SlashRequest"></a>

### SlashRequest
SlashRequest defines a slashing request for CCV consumer module


| Field | Type | Label | Description |
| ----- | ---- | ----- | ----------- |
| `packet` | [interchain_security.ccv.v1.SlashPacketData](#interchain_security.ccv.v1.SlashPacketData) |  |  |
| `downtime` | [bool](#bool) |  |  |





 <!-- end messages -->

 <!-- end enums -->

 <!-- end HasExtensions -->

 <!-- end services -->



<a name="interchain_security/ccv/consumer/v1/genesis.proto"></a>
<p align="right"><a href="#top">Top</a></p>

## interchain_security/ccv/consumer/v1/genesis.proto



<a name="interchain_security.ccv.consumer.v1.GenesisState"></a>

### GenesisState
GenesisState defines the CCV consumer chain genesis state


| Field | Type | Label | Description |
| ----- | ---- | ----- | ----------- |
| `params` | [Params](#interchain_security.ccv.consumer.v1.Params) |  |  |
| `provider_client_id` | [string](#string) |  | empty for a completely new chain |
| `provider_channel_id` | [string](#string) |  | empty for a completely new chain |
| `new_chain` | [bool](#bool) |  | true for new chain GenesisState, false for chain restart. |
| `provider_client_state` | [ibc.lightclients.tendermint.v1.ClientState](#ibc.lightclients.tendermint.v1.ClientState) |  | ProviderClientState filled in on new chain, nil on restart. |
| `provider_consensus_state` | [ibc.lightclients.tendermint.v1.ConsensusState](#ibc.lightclients.tendermint.v1.ConsensusState) |  | ProviderConsensusState filled in on new chain, nil on restart. |
| `unbonding_sequences` | [UnbondingSequence](#interchain_security.ccv.consumer.v1.UnbondingSequence) | repeated |  |
| `initial_val_set` | [tendermint.abci.ValidatorUpdate](#tendermint.abci.ValidatorUpdate) | repeated |  |






<a name="interchain_security.ccv.consumer.v1.UnbondingSequence"></a>

### UnbondingSequence
UnbondingSequence defines the genesis information for each unbonding packet sequence.


| Field | Type | Label | Description |
| ----- | ---- | ----- | ----------- |
| `sequence` | [uint64](#uint64) |  |  |
| `unbonding_time` | [uint64](#uint64) |  |  |
| `unbonding_packet` | [ibc.core.channel.v1.Packet](#ibc.core.channel.v1.Packet) |  |  |





 <!-- end messages -->

 <!-- end enums -->

 <!-- end HasExtensions -->

 <!-- end services -->



<a name="interchain_security/ccv/provider/v1/provider.proto"></a>
<p align="right"><a href="#top">Top</a></p>

## interchain_security/ccv/provider/v1/provider.proto



<a name="interchain_security.ccv.provider.v1.ConsumerAdditionProposal"></a>

### ConsumerAdditionProposal
ConsumerAdditionProposal is a governance proposal on the provider chain to spawn a new consumer chain.
If it passes, then all validators on the provider chain are expected to validate the consumer chain at spawn time
or get slashed. It is recommended that spawn time occurs after the proposal end time.


| Field | Type | Label | Description |
| ----- | ---- | ----- | ----------- |
| `title` | [string](#string) |  | the title of the proposal |
| `description` | [string](#string) |  | the description of the proposal |
| `chain_id` | [string](#string) |  | the proposed chain-id of the new consumer chain, must be different from all other consumer chain ids of the executing provider chain. |
| `initial_height` | [ibc.core.client.v1.Height](#ibc.core.client.v1.Height) |  | the proposed initial height of new consumer chain. For a completely new chain, this will be {0,1}. However, it may be different if this is a chain that is converting to a consumer chain. |
| `genesis_hash` | [bytes](#bytes) |  | genesis hash with no staking information included. |
| `binary_hash` | [bytes](#bytes) |  | binary hash is the hash of the binary that should be used by validators on chain initialization. |
| `spawn_time` | [google.protobuf.Timestamp](#google.protobuf.Timestamp) |  | spawn time is the time on the provider chain at which the consumer chain genesis is finalized and all validators will be responsible for starting their consumer chain validator node. |






<a name="interchain_security.ccv.provider.v1.HandshakeMetadata"></a>

### HandshakeMetadata



| Field | Type | Label | Description |
| ----- | ---- | ----- | ----------- |
| `provider_fee_pool_addr` | [string](#string) |  |  |
| `version` | [string](#string) |  |  |






<a name="interchain_security.ccv.provider.v1.Params"></a>

### Params
Params defines the parameters for CCV Provider module


| Field | Type | Label | Description |
| ----- | ---- | ----- | ----------- |
| `template_client` | [ibc.lightclients.tendermint.v1.ClientState](#ibc.lightclients.tendermint.v1.ClientState) |  |  |





 <!-- end messages -->

 <!-- end enums -->

 <!-- end HasExtensions -->

 <!-- end services -->



<a name="interchain_security/ccv/provider/v1/genesis.proto"></a>
<p align="right"><a href="#top">Top</a></p>

## interchain_security/ccv/provider/v1/genesis.proto



<a name="interchain_security.ccv.provider.v1.ConsumerState"></a>

### ConsumerState
ConsumerState defines the state that the provider chain stores for each consumer chain


| Field | Type | Label | Description |
| ----- | ---- | ----- | ----------- |
| `chain_id` | [string](#string) |  |  |
| `channel_id` | [string](#string) |  |  |
| `status` | [interchain_security.ccv.v1.Status](#interchain_security.ccv.v1.Status) |  |  |






<a name="interchain_security.ccv.provider.v1.GenesisState"></a>

### GenesisState
GenesisState defines the CCV provider chain genesis state


| Field | Type | Label | Description |
| ----- | ---- | ----- | ----------- |
| `consumer_states` | [ConsumerState](#interchain_security.ccv.provider.v1.ConsumerState) | repeated |  |
| `params` | [Params](#interchain_security.ccv.provider.v1.Params) |  |  |





 <!-- end messages -->

 <!-- end enums -->

 <!-- end HasExtensions -->

 <!-- end services -->



<a name="interchain_security/ccv/provider/v1/query.proto"></a>
<p align="right"><a href="#top">Top</a></p>

## interchain_security/ccv/provider/v1/query.proto



<a name="interchain_security.ccv.provider.v1.QueryConsumerGenesisRequest"></a>

### QueryConsumerGenesisRequest



| Field | Type | Label | Description |
| ----- | ---- | ----- | ----------- |
| `chain_id` | [string](#string) |  |  |






<a name="interchain_security.ccv.provider.v1.QueryConsumerGenesisResponse"></a>

### QueryConsumerGenesisResponse



| Field | Type | Label | Description |
| ----- | ---- | ----- | ----------- |
| `genesis_state` | [interchain_security.ccv.consumer.v1.GenesisState](#interchain_security.ccv.consumer.v1.GenesisState) |  |  |





 <!-- end messages -->

 <!-- end enums -->

 <!-- end HasExtensions -->


<a name="interchain_security.ccv.provider.v1.Query"></a>

### Query


| Method Name | Request Type | Response Type | Description | HTTP Verb | Endpoint |
| ----------- | ------------ | ------------- | ------------| ------- | -------- |
| `ConsumerGenesis` | [QueryConsumerGenesisRequest](#interchain_security.ccv.provider.v1.QueryConsumerGenesisRequest) | [QueryConsumerGenesisResponse](#interchain_security.ccv.provider.v1.QueryConsumerGenesisResponse) | ConsumerGenesis queries the genesis state needed to start a consumer chain whose proposal has been accepted | GET|/interchain_security/ccv/provider/consumer_genesis/{chain_id}|

 <!-- end services -->



<a name="interchain_security/ccv/v1/query.proto"></a>
<p align="right"><a href="#top">Top</a></p>

## interchain_security/ccv/v1/query.proto


 <!-- end messages -->

 <!-- end enums -->

 <!-- end HasExtensions -->


<a name="interchain_security.ccv.v1.Query"></a>

### Query
Query defines the gRPC querier service.

| Method Name | Request Type | Response Type | Description | HTTP Verb | Endpoint |
| ----------- | ------------ | ------------- | ------------| ------- | -------- |

 <!-- end services -->



<a name="interchain_security/ccv/v1/tx.proto"></a>
<p align="right"><a href="#top">Top</a></p>

## interchain_security/ccv/v1/tx.proto


 <!-- end messages -->

 <!-- end enums -->

 <!-- end HasExtensions -->


<a name="interchain_security.ccv.v1.Msg"></a>

### Msg
Msg defines the Msg service.

| Method Name | Request Type | Response Type | Description | HTTP Verb | Endpoint |
| ----------- | ------------ | ------------- | ------------| ------- | -------- |

 <!-- end services -->



## Scalar Value Types

| .proto Type | Notes | C++ | Java | Python | Go | C# | PHP | Ruby |
| ----------- | ----- | --- | ---- | ------ | -- | -- | --- | ---- |
| <a name="double" /> double |  | double | double | float | float64 | double | float | Float |
| <a name="float" /> float |  | float | float | float | float32 | float | float | Float |
| <a name="int32" /> int32 | Uses variable-length encoding. Inefficient for encoding negative numbers – if your field is likely to have negative values, use sint32 instead. | int32 | int | int | int32 | int | integer | Bignum or Fixnum (as required) |
| <a name="int64" /> int64 | Uses variable-length encoding. Inefficient for encoding negative numbers – if your field is likely to have negative values, use sint64 instead. | int64 | long | int/long | int64 | long | integer/string | Bignum |
| <a name="uint32" /> uint32 | Uses variable-length encoding. | uint32 | int | int/long | uint32 | uint | integer | Bignum or Fixnum (as required) |
| <a name="uint64" /> uint64 | Uses variable-length encoding. | uint64 | long | int/long | uint64 | ulong | integer/string | Bignum or Fixnum (as required) |
| <a name="sint32" /> sint32 | Uses variable-length encoding. Signed int value. These more efficiently encode negative numbers than regular int32s. | int32 | int | int | int32 | int | integer | Bignum or Fixnum (as required) |
| <a name="sint64" /> sint64 | Uses variable-length encoding. Signed int value. These more efficiently encode negative numbers than regular int64s. | int64 | long | int/long | int64 | long | integer/string | Bignum |
| <a name="fixed32" /> fixed32 | Always four bytes. More efficient than uint32 if values are often greater than 2^28. | uint32 | int | int | uint32 | uint | integer | Bignum or Fixnum (as required) |
| <a name="fixed64" /> fixed64 | Always eight bytes. More efficient than uint64 if values are often greater than 2^56. | uint64 | long | int/long | uint64 | ulong | integer/string | Bignum |
| <a name="sfixed32" /> sfixed32 | Always four bytes. | int32 | int | int | int32 | int | integer | Bignum or Fixnum (as required) |
| <a name="sfixed64" /> sfixed64 | Always eight bytes. | int64 | long | int/long | int64 | long | integer/string | Bignum |
| <a name="bool" /> bool |  | bool | boolean | boolean | bool | bool | boolean | TrueClass/FalseClass |
| <a name="string" /> string | A string must always contain UTF-8 encoded or 7-bit ASCII text. | string | String | str/unicode | string | string | string | String (UTF-8) |
| <a name="bytes" /> bytes | May contain any arbitrary sequence of bytes. | string | ByteString | str | []byte | ByteString | string | String (ASCII-8BIT) |

