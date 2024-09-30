---
sidebar_position: 3
---

# x/ccv/consumer

## Overview

The ICS consumer module enables consumer chains to use stake locked on a provider chain 
as collateral for their own proof-of-stake based block production. 

The consumer module established a IBC ordered channel to the provider chain. 
This channel is used by the provider chain to regularly sent validator updates the the consumer chain. 
The consumer sends these updates to its own consensus engine. 
This means that the consumer module acts as a staking module of the consumer chain. 

Regularly, the consumer module sends a part of the consumer chain's block rewards 
to the provider chain as ICS rewards.

If one of the validators in the consumer chain's validator set is missing enough blocks (i.e., downtime infraction),
the consumer module notifies the provider chain by sending an IBC packet to the provider module. 
As a result, the misbehaving validator is punished on the provider chain.

## State 

For clarity, the description of the the consumer module state is split into features.
For a more accurate description, check out the `x/ccv/consumer/types/keys.go` file, which contains the definitions of all the keys. 

### Provider Connection

#### ProviderClientID

`ProviderClientID` is the ID of the provider client on which the CCV channel is built.

Format: `byte(3) -> string`

#### ProviderChannelID

`ProviderChannelID` is the ID of the CCV channel. 

Format: `byte(4) -> string`

### Changeover

#### PreCCV

`PreCCV` is the flag set when the consumer chain is in the process of a standalone to consumer chain changeover. 

Format: `byte(7) -> uint64`

#### InitialValSet

`InitialValSet` is the initial validator set on the consumer chain.

Format: `byte(8) -> GenesisState`

Note that only the `InitialValSet` field of the `ProviderInfo` field of `GenesisState` is set, i.e., 

```proto
message GenesisState {
  ...
  ProviderInfo provider = 14
      [ (gogoproto.nullable) = false ];
}

message ProviderInfo {
  // InitialValset filled in on new chain and on restart.
  repeated .tendermint.abci.ValidatorUpdate initial_val_set = 3
      [ (gogoproto.nullable) = false ];
}
```

#### InitGenesisHeight

`InitGenesisHeight` is the height when the consumer module was initialized (i.e., the `InitGenesis` method was called). 

Format: `byte(17) -> uint64`

#### PrevStandaloneChain

`PrevStandaloneChain` is the flag set when the consumer chain was previously a standalone chain.

Format: `byte(19) -> []byte{}`

### Validator Updates

#### PendingChanges

`PendingChanges` are the validator updates received from the provider that were not yet sent to the consensus engine.

Format: `byte(5) -> ValidatorSetChangePacketData`

Note that only the `ValidatorUpdates` field of `ValidatorSetChangePacketData` is set.

#### CrossChainValidator

`CrossChainValidator` is the internal state of a consumer validator with consensus address `addr`. 

Format: `byte(16) | addr -> CrossChainValidator`, where `CrossChainValidator` is defined as 

```proto
message CrossChainValidator {
  bytes address = 1;
  int64 power = 2;
  // pubkey is the consensus public key of the validator, as a Protobuf Any.
  google.protobuf.Any pubkey = 3 [
    (cosmos_proto.accepts_interface) = "cosmos.crypto.PubKey",
    (gogoproto.moretags) = "yaml:\"consensus_pubkey\""
  ];
  // deprecated
  bool opted_out = 4 [deprecated = true];
}
```

#### HistoricalInfo

`HistoricalInfo` is the header and validator information for a given block. 
For more details, see the [Cosmos SDK docs](https://docs.cosmos.network/v0.50/build/modules/staking#historicalinfo).

Format: `byte(11) | height -> HistoricalInfo`, where `HistoricalInfo` is define in the staking module as 

```proto
message HistoricalInfo {
  tendermint.types.Header header = 1 [(gogoproto.nullable) = false, (amino.dont_omitempty) = true];
  repeated Validator      valset = 2 [(gogoproto.nullable) = false, (amino.dont_omitempty) = true];
}
```

### Reward Distribution

#### LastDistributionTransmission

`LastDistributionTransmission` is the block height of the last attempt to send ICS rewards to the provider module. 

Format: `byte(1) -> LastTransmissionBlockHeight`, where `LastTransmissionBlockHeight` is defined as 

```proto
message LastTransmissionBlockHeight { 
  int64 height = 1; 
}
```

### Downtime Infractions

#### OutstandingDowntime

`OutstandingDowntime` is the flag set when a `SlashPacket` is queued to be sent to the provider for a downtime infraction of a validator with consensus address `addr`. 
The flag is unset when receiving from the provider a `VSCPacket` with a slash acknowledgement (see `SlashAcks` in `ValidatorSetChangePacketData`).

Format: `byte(14) | addr -> []byte{}`

#### HeightValsetUpdateID

`HeightValsetUpdateID` is the validator set update ID associated with a block height.

Format: `byte(13) | height -> uint64`

#### PendingPacketsIndex

`PendingPacketsIndex` is the next index available to store packet data to be sent to the provider chain (see below). 

Format: `byte(20) -> uint64`

#### PendingDataPacketsV1

`PendingDataPacketsV1` is the queue of packet data to be sent to the provider chain.
In general, packets in this queue will be sent to the provider in the end blocker, unless 

- the CCV channel is not yet established;
- the provider client is expired;
- the last slash packet sent was not yet acknowledged by the provider chain.  

Format: `byte(15) | index -> ConsumerPacketData`, where `index` is the index of the packet in the queue and `ConsumerPacketData` is defined as 

```proto
message ConsumerPacketData {
  ConsumerPacketDataType type = 1;

  oneof data {
    SlashPacketData slashPacketData = 2;
    VSCMaturedPacketData vscMaturedPacketData = 3;
  }
}
```

#### SlashRecord

`SlashRecord` is the record storing the state of a SlashPacket sent to the provider chain that was not yet acknowledged.
See [ADR 008](../../adrs/adr-008-throttle-retries.md) for more details.

Format: `byte(21) -> SlashRecord`, where `SlashRecord` is defined as 

```proto
message SlashRecord {
  bool waiting_on_reply = 1;
  google.protobuf.Timestamp send_time = 2
      [ (gogoproto.stdtime) = true, (gogoproto.nullable) = false ];
}
```

## State Transitions

> TBA

## IBC Callbacks

The consumer module is an IBC application that implements the [IBC module callback](https://ibc.cosmos.network/v8/ibc/apps/apps/#create-a-custom-ibc-application-module).

### OnChanOpenInit

`OnChanOpenInit` first verifies that the CCV channel was not already created. 
Then, it validates the channel parameters -- an ordered IBC channel connected on the `consumer` port 
and with the counterparty port set to `provider` -- and asserts that the version matches the expected version 
(only verions `1` is supported).

Finally, it verifies that the underlying client is the expected client of the provider chain 
(i.e., provided in the consumer module genesis state). 

### OnChanOpenTry

`OnChanOpenTry` returns an error. `MsgChannelOpenTry` should be sent to the provider. 

### OnChanOpenAck

`OnChanOpenAck` first verifies that the CCV channel was not already created. 
Then it verifies that the counterparty version matches the expected version 
(only verions `1` is supported).

If the verification passes, it stores the [ProviderFeePoolAddr](#providerfeepooladdrstr) in the state.

Finally, if the [DistributionTransmissionChannel](#distributiontransmissionchannel) parameter is not set,
it initiate the opening handshake for a token transfer channel over the same connection as the CCV channel
by calling the `ChannelOpenInit` method of the IBC module.

### OnChanOpenConfirm

`OnChanOpenConfirm` returns an error. `MsgChanOpenConfirm` should be sent to the provider. 

### OnChanCloseInit

`OnChanCloseInit` allow relayers to close duplicate OPEN channels, if the channel handshake is completed.

### OnChanCloseConfirm

`OnChanCloseConfirm` is a no-op.

### OnRecvPacket

`OnRecvPacket` unmarshals the IBC packet data into a `ValidatorSetChangePacketData` struct (see below) and executes the handling logic.

- If it is the first packet received, sets the underlying IBC channel as the canonical CCV channel.
- Collects validator updates to be sent to the consensus engine at the end of the block.
- Store in state the block height to VSC id (i.e., `valset_update_id`) mapping.
- Removed the outstanding downtime flags from the validator for which the jailing 
  for downtime infractions was acknowledged by the provider chain (see the `slash_acks` field in `ValidatorSetChangePacketData`).

```proto
message ValidatorSetChangePacketData {
  repeated .tendermint.abci.ValidatorUpdate validator_updates = 1 [
    (gogoproto.nullable) = false,
    (gogoproto.moretags) = "yaml:\"validator_updates\""
  ];
  uint64 valset_update_id = 2;
  // consensus address of consumer chain validators
  // successfully jailed on the provider chain
  repeated string slash_acks = 3;
}
``` 

### OnAcknowledgementPacket

`OnAcknowledgementPacket` enables the consumer module to confirm that the provider module received 
the previously sent `SlashPacket` and it unblocks the sending of the next `SlashPacket`. 
This functionality is needed for throttling jailing on the provider chain. For more details, see [ADR-008](../../adrs/adr-008-throttle-retries.md).

### OnTimeoutPacket

`OnTimeoutPacket` is a no-op.

## Messages

### MsgUpdateParams

`MsgUpdateParams` updates the [consumer module parameters](#parameters). 
The params are updated through a governance proposal where the signer is the gov module account address.

```proto
message MsgUpdateParams {
  option (cosmos.msg.v1.signer) = "authority";

  // signer is the address of the governance account.
  string authority = 1 [(cosmos_proto.scalar) = "cosmos.AddressString"];

  // params defines the x/consumer parameters to update.
  interchain_security.ccv.v1.ConsumerParams params = 2 [(gogoproto.nullable) = false];
}
```

## BeginBlock

In the `BeginBlock` of the consumer module the following actions are performed:

- Store in state the block height to VSC id mapping needed for sending to the provider the height of infractions committed on the consumer chain.
- Track historical entries. This is the same lofic as in the `x/staking` module.

## EndBlock

In the `EndBlock` of the consumer module the following actions are performed:

- If `PreCCV` state is active, i.e., the consumer chain is a previously standalone chain
  that was just upgraded to include the consumer module, then execute the [changeover logic](../../consumer-development/changeover-procedure.md).
- Otherwise, distribute block rewards internally and once every [BlocksPerDistributionTransmission](#blocksperdistributiontransmission) send 
  ICS rewards to the provider chain.
- Send slash packets to the provider chain reporting infractions validators commited on the consumer chain.
- Send to the consensus engine validator updates reveived from the provider chain.

## Hooks

> TBA

## Events

> TBA

## Parameters

:::warning
The consumer module parameters are set by the provider when creating the consumer genesis (i.e., when launching the consumer chain). 
As a result, changes of these parameters might results in incompatibilities between different versions of consumers and providers. 
:::

The consumer module contains the following parameters.

### Enabled

`Enabled` is deprecated. 

### BlocksPerDistributionTransmission


| Type  | Default value |
| ----- | ------------- |
| int64 | 1000          |

`BlocksPerDistributionTransmission` is the number of blocks between rewards transfers from the consumer to the provider.

### DistributionTransmissionChannel

| Type   | Default value |
| ------ | ------------- |
| string | ""            |

`DistributionTransmissionChannel` is the provider chain IBC channel used for receiving consumer chain reward distribution token transfers. This is automatically set during the consumer-provider handshake procedure.

Providing an IBC transfer channel enables a consumer chain to re-use one of the existing channels to the provider for consumer chain rewards distribution. 
This will preserve the `ibc denom` that may already be in use. 
This is especially important for standalone chains transitioning to become consumer chains. 
For more details, see the [changeover procedure](../consumer-development/changeover-procedure.md).

### ProviderFeePoolAddrStr

| Type   | Default value |
| ------ | ------------- |
| string | ""            |

`ProviderFeePoolAddrStr` is the provider chain fee pool address used for receiving consumer chain reward distribution token transfers. This is automatically set during the consumer-provider handshake procedure.

### CcvTimeoutPeriod

| Type          | Default value      |
| ------------- | ------------------ |
| time.Duration | 2419200s (4 weeks) |

`CcvTimeoutPeriod` is the period used to compute the timeout timestamp when sending IBC packets. 
`CcvTimeoutPeriod` may have different values on the provider and consumer chains.

### TransferTimeoutPeriod

| Type          | Default value  |
| ------------- | -------------- |
| time.Duration | 3600s (1 hour) |

`TransferTimeoutPeriod` is the timeout period for consumer chain reward distribution IBC packets.

### ConsumerRedistributionFraction

| Type   | Default value |
| ------ | ------------- |
| string | "0.75"        |

`ConsumerRedistributionFraction` is the fraction of tokens allocated to the consumer redistribution address during distribution events. 
The fraction is a string representing a decimal number. For example `"0.75"` would represent `75%`.
For example, a consumer with `ConsumerRedistributionFraction` set to `"0.75"` would send `75%` of its block rewards and accumulated fees to the consumer redistribution address, and the remaining `25%` to the provider chain every `BlocksPerDistributionTransmission` blocks.

### HistoricalEntries

| Type  | Default value |
| ----- | ------------- |
| int64 | 10000         |

`HistoricalEntries` is the number of historical info entries to persist in store (see the staking module parameter with the same name for details). 
`HistoricalEntries` is needed since the consumer module acts as a staking module on the consumer chain.

### UnbondingPeriod

| Type          | Default value      |
| ------------- | ------------------ |
| time.Duration | 1209600s (2 weeks) |

`UnbondingPeriod` is the unbonding period on the consumer chain.
It is recommended that every consumer chain set and unbonding period shorter than provider unbonding period, e.g., one week shorter. 

### SoftOptOutThreshold

`SoftOptOutThreshold` is deprecated.

### RewardDenoms

| Type     | Default value |
| -------- | ------------- |
| []string | []string{}    |

`RewardDenoms` are the denominations which are allowed to be sent to the provider as ICS rewards.

### ProviderRewardDenoms

| Type     | Default value |
| -------- | ------------- |
| []string | []string{}    |

`ProviderRewardDenoms` are the denominations coming from the provider which are allowed to be used as ICS rewards. e.g. "uatom".

### RetryDelayPeriod

| Type          | Default value  |
| ------------- | -------------- |
| time.Duration | 3600s (1 hour) |

`RetryDelayPeriod` is the period at which the consumer retries to send a `SlashPacket` that was rejected by the provider.
For more details, see [ADR-008](../adrs/adr-008-throttle-retries.md).

## Client

### CLI

A user can interact with the `consumer` module using the CLI.

#### Query

The `query` commands allow users to query `consumer` state.

##### Next Fee Distribution

The `next-fee-distribution` command allows to query next fee distribution data.

```bash
interchain-security-cd query ccvconsumer next-fee-distribution [flags]
```

Example:

```bash
interchain-security-cd query ccvconsumer next-fee-distribution
```

Example Output:

```bash
data:
  currentHeight: "967"
  distribution_fraction: "0.75"
  lastHeight: "960"
  nextHeight: "980"
  toConsumer: ""
  toProvider: ""
  total: ""
```

##### Provider Info

The `provider-info` command allows to query provider info.

```bash
interchain-security-cd query ccvconsumer provider-info [flags]
```

Example:

```bash
interchain-security-cd query ccvconsumer provider-info
```

Example Output:

```bash
provider_address: "cosmos1abcd1234..."
```

##### Throttle State

The `throttle-state` command allows to query throttle state.

```bash
interchain-security-cd query ccvconsumer provider-info [flags]
```

Example:

```bash
interchain-security-cd query ccvconsumer provider-info
```

Example Output:

```bash
packet_data_queue: []
slash_record: null
```

##### Params

The `params` command allows to query consumer module parameters.

```bash
interchain-security-cd query ccvconsumer params [flags]
```

Example:

```bash
interchain-security-cd query ccvconsumer params
```

Example Output:

```bash
provider_address: "cosmos1abcd1234..."
```

### gRPC

A user can query the `consumer` module using gRPC endpoints.

#### Next Fee Distribution

The `QueryNextFeeDistribution` endpoint queries next fee distribution data.

```bash
interchain_security.ccv.consumer.v1.Query/QueryNextFeeDistribution
```

Example:

```bash
grpcurl -plaintext localhost:9090 interchain_security.ccv.consumer.v1.Query/QueryNextFeeDistribution
```

Example Output:

```json
{
  "data": {
    "currentHeight": "402",
    "lastHeight": "400",
    "nextHeight": "420",
    "distributionFraction": "0.75"
  }
}
```

#### Provider Info

The `QueryProviderInfo` endpoint queries provider info.

```bash
interchain_security.ccv.consumer.v1.Query/QueryProviderInfo
```

Example:

```bash
grpcurl -plaintext interchain_security.ccv.consumer.v1.Query/QueryProviderInfo
```

Example Output:

```json
{
  "consumer": {
    "chainID": "pion-1",
    "clientID": "07-tendermint-0",
    "connectionID": "connection-0",
    "channelID": "channel-0"
  },
  "provider": {
    "chainID": "provider",
    "clientID": "07-tendermint-0",
    "connectionID": "connection-0",
    "channelID": "channel-0"
  }
}
```

#### Throttle State

The `QueryThrottleState` endpoint queries throttle state.

```bash
interchain_security.ccv.consumer.v1.Query/QueryThrottleState
```

Example:

```bash
grpcurl -plaintext localhost:9090 interchain_security.ccv.consumer.v1.Query/QueryThrottleState
```

Example Output:

```json
{
  "consumer": {
    "chainID": "pion-1",
    "clientID": "07-tendermint-0",
    "connectionID": "connection-0",
    "channelID": "channel-0"
  },
  "provider": {
    "chainID": "provider",
    "clientID": "07-tendermint-0",
    "connectionID": "connection-0",
    "channelID": "channel-0"
  }
}
```

#### Params

The `QueryParams` endpoint queries consumer module parameters.

```bash
interchain_security.ccv.consumer.v1.Query/QueryParams
```

Example:

```bash
grpcurl -plaintext localhost:9090 interchain_security.ccv.consumer.v1.Query/QueryParams
```

Example Output:

```bash
```

### REST

A user can query the `consumer` module using REST endpoints.

#### Next Fee Distribution

The `next-fee-distribution` endpoint queries next fee distribution data.

```bash
/interchain_security/ccv/consumer/next-fee-distribution
```

Example:

```bash
curl http://localhost:1317/interchain_security/ccv/consumer/next-fee-distribution
```

Example Output:

```json
{
  "data": {
    "currentHeight": "402",
    "lastHeight": "400",
    "nextHeight": "420",
    "distributionFraction": "0.75"
  }
}
```

#### Provider Info

The `QueryProviderInfo` endpoint queries provider info.

```bash
/interchain_security/ccv/consumer/provider-info
```

Example:

```bash
curl http://localhost:1317/interchain_security/ccv/consumer/provider-info
```

Example Output:

```json
{
  "consumer": {
    "chainID": "pion-1",
    "clientID": "07-tendermint-0",
    "connectionID": "connection-0",
    "channelID": "channel-0"
  },
  "provider": {
    "chainID": "provider",
    "clientID": "07-tendermint-0",
    "connectionID": "connection-0",
    "channelID": "channel-0"
  }
}
```

#### Throttle State

The `throttle_state` endpoint queries throttle state.

```bash
/interchain_security/ccv/consumer/throttle_state
```

Example:

```bash
curl http://localhost:1317/interchain_security/ccv/consumer/throttle_state
```

Example Output:

```json
{
  "consumer": {
    "chainID": "pion-1",
    "clientID": "07-tendermint-0",
    "connectionID": "connection-0",
    "channelID": "channel-0"
  },
  "provider": {
    "chainID": "provider",
    "clientID": "07-tendermint-0",
    "connectionID": "connection-0",
    "channelID": "channel-0"
  }
}
```

#### Params

The `params` endpoint queries consumer module parameters.

```bash
/interchain_security/ccv/consumer/params
```

Example:

```bash
curl http://localhost:1317/interchain_security/ccv/consumer/params
```

Example Output:

```bash
```