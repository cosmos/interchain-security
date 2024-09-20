---
sidebar_position: 2
---

# x/ccv/provider

## Overview

The ICS provider module enables a proof-of-stake chain (known as the provider chain) 
to share (parts of) its security with other chains (known as consumer chains).
This basically mean that consumer chains can run as proof-of-stake chains using 
(parts of) the stake locked on the provider as collateral.  

The provider module has the following functionalities:

- The permissionless creation of consumer chains.
- The customization of the consumer chains validator sets. 
- The option for validators to opt in to validate the consumer chains they want.
- The distribution of rewards from consumer chains to the opted in validators.
- The slashing and jailing of validators commiting infractions on consumer chains based on cryptographic evidence.

## State 

For clarity, the description of the the provider module state is split into features.
For a more accurate description, check out the `x/ccv/provider/types/keys.go` file, which contains the definitions of the keys. 

### Consumer Lifecycle

#### ConsumerId

`ConsumerId` is the consumer ID of the next consumer chain to be created.

Format: `byte(43) -> uint64`

#### ConsumerIdToChainId

`ConsumerIdToChainId` is the chain ID of a given consumer chain. 

Format: `byte(44) | len(consumerId) | []byte(consumerId) -> string`

#### ConsumerIdToOwnerAddress

`ConsumerIdToOwnerAddress` is the account address of the owner of a given consumer chain. 

Format: `byte(45) | len(consumerId) | []byte(consumerId) -> string`

#### ConsumerIdToMetadataKey

`ConsumerIdToMetadataKey` is the metadata of a given consumer chain. 

Format: `byte(46) | len(consumerId) | []byte(consumerId) -> ConsumerMetadata`

#### ConsumerIdToPhase

`ConsumerIdToPhase` is the phase of a given consumer chain. 

Format: `byte(49) | len(consumerId) | []byte(consumerId) -> ConsumerPhase`, where `ConsumerPhase` is defined as 

```proto
enum ConsumerPhase {
  option (gogoproto.goproto_enum_prefix) = false;

  // UNSPECIFIED defines an empty phase.
  CONSUMER_PHASE_UNSPECIFIED = 0;
  // REGISTERED defines the phase in which a consumer chain has been assigned a unique consumer id.
  // A chain in this phase cannot yet launch.
  CONSUMER_PHASE_REGISTERED = 1;
  // INITIALIZED defines the phase in which a consumer chain has set all the needed parameters to launch but
  // has not yet launched (e.g., because the `spawnTime` of the consumer chain has not yet been reached).
  CONSUMER_PHASE_INITIALIZED = 2;
  // LAUNCHED defines the phase in which a consumer chain is running and consuming a subset of the validator
  // set of the provider.
  CONSUMER_PHASE_LAUNCHED = 3;
  // STOPPED defines the phase in which a previously-launched chain has stopped.
  CONSUMER_PHASE_STOPPED = 4;
  // DELETED defines the phase in which the state of a stopped chain has been deleted.
  CONSUMER_PHASE_DELETED = 5;
}
```

#### ConsumerIdToRemovalTime

`ConsumerIdToRemovalTime` is the removal time of a given consumer chain in the stopped phase. 

Format: `byte(50) | len(consumerId) | []byte(consumerId) -> time.Time`

#### SpawnTimeToConsumerIds

`SpawnTimeToConsumerIds` are the IDs of initialized consumer chains ready to be launched at a timestamp `ts`. 

Format: `byte(51) | ts -> ConsumerIds`, where `ConsumerIds` is defined as 

```proto
message ConsumerIds { 
  repeated string ids = 1; 
}
```

#### RemovalTimeToConsumerIds

`RemovalTimeToConsumerIds` are the IDs of stopped consumer chains ready to be removed at a timestamp `ts`. 

Format: `byte(52) | ts -> ConsumerIds`, where `ConsumerIds` is defined as 

### Consumer Launch

#### ConsumerIdToInitializationParameters

`ConsumerIdToInitializationParameters` are the initialization parameters of a given consumer chain. 

Format: `byte(47) | len(consumerId) | []byte(consumerId) -> ConsumerInitializationParameters`

#### ConsumerIdToChannelId

`ConsumerIdToChannelId` is the ID of the CCV channel associated with a consumer chain. 

Format: `byte(5) | []byte(consumerId) -> string`

#### ChannelIdToConsumerId

`ChannelIdToConsumerId` is the consumer ID associated with a CCV channel. 

Format: `byte(6) | []byte(channelId) -> string`

#### ConsumerIdToClientId

`ConsumerIdToClientId` is the ID of the client associated with a consumer chain. 
This is the underlying client of the corresponding CCV channel.

Format: `byte(7) | []byte(consumerId) -> string`

#### ClientIdToConsumerId

`ClientIdToConsumerId` is the consumer ID associated with an IBC client (i.e., the underlying client of the corresponding CCV channel).

Format: `byte(53) | len(clientId) | []byte(clientId) -> string`

#### ConsumerGenesis

`ConsumerGenesis` is the genesis state of the consumer module associated with a consumer chain.

Format: `byte(14) | []byte(consumerId) -> ConsumerGenesisState`


### Key Assingment

#### ConsumerValidators

> TODO: `ConsumerValidators` and `ConsumerValidator` are too similar. 

`ConsumerValidators` is the public key assigned by a given validator with `addr` as its provider consensus address (i.e., `sdk.ConsAddress`) on a given consumer chain.

Format: `byte(22) | len(consumerId) | []byte(consumerId) | addr -> crypto.PublicKey`, where `crypto` is `"github.com/cometbft/cometbft/proto/tendermint/crypto"`.

#### ValidatorsByConsumerAddr

`ValidatorsByConsumerAddr` is the consensus address on the provider chain of a validator with `addr` as its consensus address on a given consumer chain.

Format: `byte(23) | len(consumerId) | []byte(consumerId) | addr -> sdk.ConsAddress`.

#### ConsumerAddrsToPruneV2

`ConsumerAddrsToPruneV2` stores the list of consumer consensus addresses that can be prunned at a timestamp `ts` as they are no longer needed.

Format: `byte(40) | len(consumerId) | []byte(consumerId) | ts -> AddressList`, where `AddressList` is defined as 

```proto
message AddressList { 
  repeated bytes addresses = 1; 
}
```

### Power Shaping

#### ConsumerIdToPowerShapingParameters

`ConsumerIdToPowerShapingParameters` are the power-shaping parameters of a given consumer chain. 

Format: `byte(48) | len(consumerId) | []byte(consumerId) -> PowerShapingParameters`

#### ConsumerValidator

`ConsumerValidator` is the `ConsensusValidator` record of a provider validator on a given consumer chain, i.e., 

```proto
message ConsensusValidator {
  // validator's consensus address on the provider chain
  bytes provider_cons_addr = 1;
  // voting power the validator has during this epoch
  int64 power = 2;
  // public key the validator uses on the consumer chain during this epoch
  tendermint.crypto.PublicKey public_key = 3;
  // height the validator had when it FIRST became a consumer validator
  int64 join_height = 4;
}
```

Format: `byte(31) | len(consumerId) | []byte(consumerId) | addr -> ConsensusValidator`, with `addr` the validator's consensus address on the provider chain.

#### OptedIn

`OptedIn` is the list of provider validators that opted in to validate on a given consumer chain. 
Note that opting in doesn't guarantee a spot in the consumer validator set.

Format: `byte(32) | len(consumerId) | []byte(consumerId) | addr -> []byte{}`, with `addr` the validator's consensus address on the provider chain.

#### Allowlist

`Allowlist` is the list of provider validators that are eligible to validate a given consumer chain.

Format: `byte(36) | len(consumerId) | []byte(consumerId) | addr -> []byte{}`, with `addr` the validator's consensus address on the provider chain.

#### Denylist

`Denylist` is the list of provider validators that are not eligible to validate a given consumer chain. 
Note that validator can opt in regardless of whether they are eligible or not.

Format: `byte(37) | len(consumerId) | []byte(consumerId) | addr -> []byte{}`, with `addr` the validator's consensus address on the provider chain.

#### MinimumPowerInTopN

`MinimumPowerInTopN` is the minimum voting power a provider validator must have to be required to validate a given TopN consumer chain. 

Format: `byte(40) | len(consumerId) | []byte(consumerId) -> uint64`

### Validator Set Updates

#### ValidatorSetUpdateId

`ValidatorSetUpdateId` is an incrementing sequence number that is used as a unique identifier for validator set updates sent to the consumer chains. 
The validator set update ID is incremented every epoch. 

Format: `byte(2) -> uint64`

#### PendingVSCs

`PendingVSCs` is the list of `VSCPackets` that are queued to be sent to a given consumer chain. 

Format: `byte(17) | []byte(consumerId) -> ValidatorSetChangePackets`, where `ValidatorSetChangePackets` is defined as 

```proto
message ValidatorSetChangePackets {
  repeated ValidatorSetChangePacketData list = 1
      [ (gogoproto.nullable) = false ];
}
```

#### LastProviderConsensusVals

`LastProviderConsensusVals` is the last validator set sent to the consensus engine of the provider chain.

Format: `byte(42) | addr -> ConsensusValidator`, with `addr` the validator's consensus address on the provider chain and `ConsensusValidator` defined as

```proto
message ConsensusValidator {
  // validator's consensus address on the provider chain
  bytes provider_cons_addr = 1;
  // voting power the validator has during this epoch
  int64 power = 2;
  // public key the validator uses on the consumer chain during this epoch
  tendermint.crypto.PublicKey public_key = 3;
  // height the validator had when it FIRST became a consumer validator
  int64 join_height = 4;
}
```

### Reward Distribution

#### ConsumerRewardDenoms

`ConsumerRewardDenoms` is storing the list of whitelisted denoms that are accepted as ICS rewards. 
Note that denoms that are not whitelisted can still be transfer to the `consumer_rewards_pool` account on the provider module, but they will not be distributed to validators and their delegators. 

Format: `byte(27) | []byte(denom) -> []byte{}`

#### ConsumerRewardsAllocation

`ConsumerRewardsAllocation` is the allocation of ICS rewards for a given consumer chain. 
This is used to distribute ICS rewards only to the validators that are part of the consumer chain validator set. 

Format: `byte(38) | []byte(consumerId) -> ConsumerRewardsAllocation`, where `ConsumerRewardsAllocation` is defined as 

```proto
message ConsumerRewardsAllocation {
  repeated cosmos.base.v1beta1.DecCoin rewards = 1 [
    (gogoproto.nullable)     = false,
    (amino.dont_omitempty)   = true,
    (gogoproto.castrepeated) = "github.com/cosmos/cosmos-sdk/types.DecCoins"
  ];
}
```

####  ConsumerCommissionRate

`ConsumerCommissionRate` is the commission rate set by a provider validator for a given consumer chain. 

Format: `byte(39) | len(consumerId) | []byte(consumerId) | addr -> math.LegacyDec`, with `addr` the validator's consensus address on the provider chain and `math` is `"cosmossdk.io/math"`.

### Consumer Infractions

#### SlashMeter

`SlashMeter` is the meter used for the throttling mechanism as the allowance of voting power that can be jailed over time. 
It is decremented by the amount of voting power jailed whenever a validator is jailed for downtime, and periodically replenished as decided by on-chain params. 
See [ADR 002](../../adrs/adr-002-throttle.md) for more details.

Format: `byte(3) -> math.Int` 

#### SlashMeterReplenishTimeCandidate

`SlashMeterReplenishTimeCandidate` is the next UTC time the `SlashMeter` could potentially be replenished. 
Note that this value is the next time the `SlashMeter` will be replenished if and only if the `SlashMeter` is not full. 
Otherwise this value will be updated in every future block until the slash meter becomes not full.

Format: `byte(4) -> time.Time`

#### ValsetUpdateBlockHeight

`ValsetUpdateBlockHeight` is the block height associated with a validator set update ID `vscId`. 
This is used for mapping infraction heights on consumer chains to heights on the provider chain via the validator set update IDs (together with [InitChainHeight](#initchainheight)). 

Format: `byte(13) | vscId -> uint64`

#### InitChainHeight

`InitChainHeight` is the block height on the provider when the CCV channel of a given consumer chain was established (i.e., the channel opening handshake was completed).
This is used for mapping infraction heights on consumer chains to heights on the provider chain (together with [ValsetUpdateBlockHeight](#valsetupdateblockheight)). 

Format: `byte(16) | []byte(consumerId) -> uint64`

#### SlashAcks

`SlashAcks` are addresses of validators for which `SlashPackets` for downtime infractions received from a given consumer chain were handled.
These addresses are sent together with the validator updates to the consumer chain as confirmation that the downtime infractions were dealt with. 

Format: `byte(15) | []byte(consumerId) -> SlashAcks`, where `SlashAcks` is defined as

```proto
message SlashAcks { 
  repeated string addresses = 1; 
}
```

#### EquivocationEvidenceMinHeight

`EquivocationEvidenceMinHeight` is the minimum height of a valid evidence of equivocation on a given consumer chain. 

Format: `byte(29) | []byte(consumerId) -> uint64`

## State Transitions

### Consumer chain phases

The following diagram describes the phases of a consumer chain from the perspective of the provider module:

![Phases of a consumer chain](../../adrs/figures/adr19_phases_of_a_consumer_chain.png)

## IBC Callbacks

The consumer module is an IBC application that implements the [IBC module callback](https://ibc.cosmos.network/v8/ibc/apps/apps/#create-a-custom-ibc-application-module).

### OnChanOpenInit

`OnChanOpenInit` returns an error. `MsgChannelOpenInit` should be sent to the consumer. 

### OnChanOpenTry

`OnChanOpenTry` validates the parameters of the _CCV channel_ -- an ordered IBC channel connected on the `provider` port 
and with the counterparty port set to `consumer` -- and asserts that the counterparty version matches the expected version 
(only verions `1` is supported).

If the validation passes, the provider module verifies that the underlying client is the expected client of the consumer chain 
(i.e., the client created during the consumer chain launch) and that no other CCV channel exists for this consumer chain.

Finally, it sets the [ProviderFeePoolAddr](./03-consumer.md#providerfeepooladdrstr) as part of the metadata.

### OnChanOpenAck

`OnChanOpenAck` returns an error. `MsgChannelOpenAck` should be sent to the consumer. 

### OnChanOpenConfirm

`OnChanOpenConfirm` first verifies that no other CCV channel exists for this consumer chain. Note that this is a sanity check.
Then, it sets the channel mapping in the state.

### OnChanCloseInit

`OnChanCloseInit` returns an error. `MsgChannelCloseInit` should be sent to the consumer. 

### OnChanCloseConfirm

`OnChanCloseConfirm` is a no-op.

### OnRecvPacket

`OnRecvPacket` unmarshals the IBC packet data into a `SlashPacketData` struct (see below) and executes the handling logic.

- Validate the fields in `SlashPacketData`:
  - `validator` has a valid address and a non-zero power;
  - `infraction` is either downtime or double-singing;
  - the provider has in state a mapping from `valset_update_id` to a block height.
- If it is a double-signing infraction, then just log it and return.
- Verify that the consumer chain is launched and the validator is opted in. 
- Update the meter used for jail throttling. 
- Jail the validator on the provider chain. 
- Store in state the ACK that the downtime infraction was handled. 
  This will be sent to the consumer with the next validator updates to enable it 
  to send other downtime infractions for this validator.

```proto
message SlashPacketData {
  tendermint.abci.Validator validator = 1 [
    (gogoproto.nullable) = false,
    (gogoproto.moretags) = "yaml:\"validator\""
  ];
  // map to the infraction block height on the provider
  uint64 valset_update_id = 2;
  // tell if the slashing is for a downtime or a double-signing infraction
  cosmos.staking.v1beta1.Infraction infraction = 3;
}
```

Note that IBC packets with `VSCMaturedPacketData` data are dropped. For more details, check out [ADR 018](../../adrs/adr-018-remove-vscmatured.md).

### OnAcknowledgementPacket

`OnAcknowledgementPacket` stops and eventually removes the consumer chain associated with the channel on which the `MsgAcknowledgement` message was received.

### OnTimeoutPacket

`OnTimeoutPacket` stops and eventually removes the consumer chain associated with the channel on which the `MsgTimeout` message was received.

## Messages

### MsgUpdateParams

`MsgUpdateParams` updates the [provider module parameters](#parameters). 
The params are updated through a governance proposal where the signer is the gov module account address.

```proto
message MsgUpdateParams {
  option (cosmos.msg.v1.signer) = "authority";

  // authority is the address of the governance account.
  string authority = 1 [(cosmos_proto.scalar) = "cosmos.AddressString"];

  // params defines the x/provider parameters to update.
  Params params = 2 [(gogoproto.nullable) = false];
}
```

### ChangeRewardDenomsProposal

`MsgChangeRewardDenoms` updates the list of whitelisted denoms accepted by the provider as ICS rewards. 
The list of accepted denoms is updated through a governance proposal where the signer is the gov module account address.

Note that this message replaces `ChangeRewardDenomsProposal`, which is deprecated. 

```proto
message MsgChangeRewardDenoms {
  option (cosmos.msg.v1.signer) = "authority";

  // the list of consumer reward denoms to add
  repeated string denoms_to_add = 1;
  // the list of consumer reward denoms to remove
  repeated string denoms_to_remove = 2;
  // signer address
  string authority = 3 [(cosmos_proto.scalar) = "cosmos.AddressString"];
}
```

### MsgCreateConsumer

`MsgCreateConsumer` enables a user to create a consumer chain. 

Both the `chain_id` and `metadata` fields are mandatory. 
Both the `initialization_parameters` and `power_shaping_parameters` fields are optional. 
The parameters not provided are set to their zero value.

The owner of the created consumer chain is the submitter of the message.
This message cannot be submitted as part of a governance proposal, i.e., the submitter cannot be the gov module account address.
As a result, if the `power_shaping_parameters` are provided, then `power_shaping_parameters.top_N` must be set to zero (i.e., opt-in consumer chain).

To create a top-n consumer chain, the following steps are require:

- Create a opt-in consumer chain (via `MsgCreateConsumer`).
- Change the ownership of the consuemr chain to the gov module account address (via `MsgUpdateConsumer`).
- Change `power_shaping_parameters.top_N` to a value in `[50, 100]` trough a governance proposal with a `MsgUpdateConsumer` message.

If the `initialization_parameters` field is set and `initialization_parameters.spawn_time > 0`, then the consumer chain will be scheduled to launch at `spawn_time`.

```proto
message MsgCreateConsumer {
  option (cosmos.msg.v1.signer) = "submitter";

  // Submitter address. If the message is successfully handled, the ownership of 
  // the consumer chain will given to this address.
  string submitter = 1 [(cosmos_proto.scalar) = "cosmos.AddressString"];

  // the chain id of the new consumer chain
  string chain_id = 2;

  ConsumerMetadata metadata = 3 [ (gogoproto.nullable) = false ];

  ConsumerInitializationParameters initialization_parameters = 4;

  PowerShapingParameters power_shaping_parameters = 5;
}
```

### MsgUpdateConsumer

`MsgUpdateConsumer` enables the owner of a consumer chain to update its parameters (e.g., set a new owner). 

Note that only the `owner` (i.e., signer) and `consumer_id` fields are mandatory. 
The others field are optional. Not providing one of them will leave the existing values unchanged. 
Providing one of `metadata`, `initialization_parameters` or `power_shaping_parameters`, 
will update all the containing fields. 
If one of the containing fields is missing, it will be set to its zero value.
For example, updating the `initialization_parameters` without specifying the `spawn_time`, will set the `spawn_time` to zero.

If the `initialization_parameters` field is set and `initialization_parameters.spawn_time > 0`, then the consumer chain will be scheduled to launch at `spawn_time`.
Updating the `spawn_time` from a positive value to zero will remove the consumer chain from the list of scheduled to launch chains. 
If the consumer chain is already launched, updating the `initialization_parameters` is no longer possible.

If the `power_shaping_parameters` field is set and `power_shaping_parameters.top_N` is possitive, then the owner needs to be the gov module account address.

If the `new_owner_address` field is set to a value different than the gov module account address, then `top_N` needs to be zero.

```proto
message MsgUpdateConsumer {
  option (cosmos.msg.v1.signer) = "owner";

  // the address of the owner of the consumer chain to be updated
  string owner = 1 [(cosmos_proto.scalar) = "cosmos.AddressString"];

  // the consumer id of the consumer chain to be updated
  string consumer_id = 2;

  // the new owner of the consumer when updated
  string new_owner_address = 3 [(cosmos_proto.scalar) = "cosmos.AddressString"];

  // the metadata of the consumer when updated
  ConsumerMetadata metadata = 4;

  // initialization parameters can only be updated before a chain has launched
  ConsumerInitializationParameters initialization_parameters = 5;

  // the power-shaping parameters of the consumer when updated
  PowerShapingParameters power_shaping_parameters = 6;
}
```

### MsgRemoveConsumer

`MsgRemoveConsumer` enables the owner of a _launched_ consumer chain to remove it from the provider chain. 
The message will first stop the consumer chain, which means the provider will stop sending it validator updates over IBC.
Then, once the unbonding period elapses, the consumer chain is removed from the provider state. 

```proto
message MsgRemoveConsumer {
  option (cosmos.msg.v1.signer) = "owner";

  // the consumer id of the consumer chain to be stopped
  string consumer_id = 1;
  // the address of the owner of the consumer chain to be stopped
  string owner = 2 [(cosmos_proto.scalar) = "cosmos.AddressString"];
}
```

### MsgOptIn

`MsgOptIn` enables a validator to opt in to validate a consumer chain. 
Note that _validators can opt in to validate consumer chains that are not launched yet_.
The signer of the message needs to match the validator address on the provider.

Note that opting in doesn't guarantee a spot in the consumer chain's validator set. 
Use the `has-to-validate` query to check if the validator is part of the consumer chain's validator set.
For more details, check out the [validator guide to Partial Set Security](../../validators/partial-set-security-for-validators.md).

Note that since the introduction of the 
[Permissionless ICS feature](https://cosmos.github.io/interchain-security/adrs/adr-019-permissionless-ics) 
the `chain_id` field is deprecated. 
Users should use `consumer_id` instead. 
You can use the `list-consumer-chains` query to get the list of all consumer chains and their consumer IDs.

The `consumer_key` field is optional. 
It enables the validator to set the consensus public key to use on the consumer chain.
The validator can assing (or re-assing) this key also later via [MsgAssignConsumerKey](#msgassignconsumerkey).

:::warning
Validators are strongly recommended to assign a separate key for each consumer chain
and **not** reuse the provider key across consumer chains for security reasons.

This is especially important since the introduction of the 
[Permissionless ICS feature](https://cosmos.github.io/interchain-security/adrs/adr-019-permissionless-ics) 
that allows multiple consumer chains to have the same chain ID. 
A validator using the same consensus key to validate on two chains with the same chain ID might get slashed for double signing. 
:::

```proto
message MsgOptIn {
  option (gogoproto.equal) = false;
  option (gogoproto.goproto_getters) = false;
  option (cosmos.msg.v1.signer) = "signer";

  // [DEPRECATED] use `consumer_id` instead
  string chain_id = 1 [deprecated = true];
  // the validator address on the provider
  string provider_addr = 2 [ (gogoproto.moretags) = "yaml:\"address\"" ];
  // (optional) The consensus public key to use on the consumer in json string format corresponding to proto-any,
  // for example `{"@type":"/cosmos.crypto.ed25519.PubKey","key":"Ui5Gf1+mtWUdH8u3xlmzdKID+F3PK0sfXZ73GZ6q6is="}`.
  // This field is optional and can remain empty (i.e., `consumer_key = ""`). A validator can always change the
  // consumer public key at a later stage by issuing a `MsgAssignConsumerKey` message.
  string consumer_key = 3;
  // submitter address
  string signer = 4 [(cosmos_proto.scalar) = "cosmos.AddressString"];
  // the consumer id of the consumer chain to opt in to
  string consumer_id = 5;
}
```

### MsgAssignConsumerKey

`MsgAssignConsumerKey` enables a validator to assign the consensus public key to use on a consumer chain.
Without assigning a specific key, the validator will need to use the same key as on the provider chain. 

:::warning
Validators are strongly recommended to assign a separate key for each consumer chain
and **not** reuse the provider key across consumer chains for security reasons.

This is especially important since the introduction of the 
[Permissionless ICS feature](https://cosmos.github.io/interchain-security/adrs/adr-019-permissionless-ics) 
that allows multiple consumer chains to have the same chain ID. 
A validator using the same consensus key to validate on two chains with the same chain ID might get slashed for double signing. 
:::

The signer of the message needs to match the validator address on the provider. 

Note that since the introduction of the 
[Permissionless ICS feature](https://cosmos.github.io/interchain-security/adrs/adr-019-permissionless-ics) 
the `chain_id` field is deprecated. 
Users should use `consumer_id` instead. 
You can use the `list-consumer-chains` query to get the list of all consumer chains and their consumer IDs.

For more details, check out the [description of the Key Assignment feature](../../features/key-assignment.md).

```proto
message MsgAssignConsumerKey {
  option (cosmos.msg.v1.signer) = "signer";
  option (gogoproto.equal) = false;
  option (gogoproto.goproto_getters) = false;


  // [DEPRECATED] use `consumer_id` instead
  string chain_id = 1 [deprecated = true];
  // The validator address on the provider
  string provider_addr = 2 [ (gogoproto.moretags) = "yaml:\"address\"" ];
  // The consensus public key to use on the consumer.
  // in json string format corresponding to proto-any, ex:
  // `{"@type":"/cosmos.crypto.ed25519.PubKey","key":"Ui5Gf1+mtWUdH8u3xlmzdKID+F3PK0sfXZ73GZ6q6is="}`
  string consumer_key = 3;

  string signer = 4 [(cosmos_proto.scalar) = "cosmos.AddressString"];

  // the consumer id of the consumer chain to assign a consensus public key to
  string consumer_id = 5;
}
```
### MsgOptOut

`MsgOptOut` enables a validator to opt out from validating a launched consumer chain. 
The signer of the message needs to match the validator address on the provider. 

Note that since the introduction of the 
[Permissionless ICS feature](https://cosmos.github.io/interchain-security/adrs/adr-019-permissionless-ics) 
the `chain_id` field is deprecated. 
Users should use `consumer_id` instead. 
You can use the `list-consumer-chains` query to get the list of all consumer chains and their consumer IDs.

For more details on optin out, check out the [validator guide to Partial Set Security](../../validators/partial-set-security-for-validators.md).

```proto
message MsgOptOut {
  option (gogoproto.equal) = false;
  option (gogoproto.goproto_getters) = false;
  option (cosmos.msg.v1.signer) = "signer";

  // [DEPRECATED] use `consumer_id` instead
  string chain_id = 1 [deprecated = true];
  // the validator address on the provider
  string provider_addr = 2 [ (gogoproto.moretags) = "yaml:\"address\"" ];
  // submitter address
  string signer = 3 [(cosmos_proto.scalar) = "cosmos.AddressString"];
  // the consumer id of the consumer chain to opt out from
  string consumer_id = 4;
}
```

### MsgSetConsumerCommissionRate

`MsgSetConsumerCommissionRate` enables validators to set a per-consumer chain commission rate. 
The `rate` is a decimal in `[minRate, 1]`, with `minRate` corresponding to the minimum commission rate set on the
provider chain (see `min_commission_rate` in `interchain-security-pd query staking params`).

The signer of the message needs to match the validator address on the provider. 

Note that since the introduction of the 
[Permissionless ICS feature](https://cosmos.github.io/interchain-security/adrs/adr-019-permissionless-ics) 
the `chain_id` field is deprecated. 
Users should use `consumer_id` instead. 
You can use the `list-consumer-chains` query to get the list of all consumer chains and their consumer IDs.

For more details on setting per-consumer chain commission rates, check out the [validator guide to Partial Set Security](../../validators/partial-set-security-for-validators.md).

```proto
message MsgSetConsumerCommissionRate {
  option (gogoproto.equal) = false;
  option (gogoproto.goproto_getters) = false;
  option (cosmos.msg.v1.signer) = "signer";

  // The validator address on the provider
  string provider_addr = 1 [ (gogoproto.moretags) = "yaml:\"address\"" ];
  // [DEPRECATED] use `consumer_id` instead
  string chain_id = 2 [deprecated = true];
  // The rate to charge delegators on the consumer chain, as a fraction
  string rate = 3 [
    (cosmos_proto.scalar)  = "cosmos.Dec",
    (gogoproto.customtype) = "cosmossdk.io/math.LegacyDec",
    (gogoproto.nullable)   = false
    ];
  // submitter address
  string signer = 4 [(cosmos_proto.scalar) = "cosmos.AddressString"];
  // the consumer id of the consumer chain to set the commission rate
  string consumer_id = 5;
}
```

### MsgSubmitConsumerMisbehaviour

`MsgSubmitConsumerMisbehaviour` enables users to submit to the provider evidence of a light client attack that occured on a consumer chain. 
This message can be submitted directly by users, e.g., via the CLI command `tx provider submit-consumer-misbehaviour`, 
or by a relayer that can be set to automatically detect consumer chain misbehaviors, e.g., [Hermes](https://github.com/informalsystems/hermes).

Note that since the introduction of the 
[Permissionless ICS feature](https://cosmos.github.io/interchain-security/adrs/adr-019-permissionless-ics) 
the `chain_id` field is deprecated. 
Users should use `consumer_id` instead. 
You can use the `list-consumer-chains` query to get the list of all consumer chains and their consumer IDs.

For more details on reporting light client attacks that occured on consumer chains, check out the [guide on equivocation infractions](../../features/slashing.md#equivocation-infractions).

```proto
message MsgSubmitConsumerMisbehaviour {
  option (cosmos.msg.v1.signer) = "submitter";
  option (gogoproto.equal) = false;
  option (gogoproto.goproto_getters) = false;

  string submitter = 1 [(cosmos_proto.scalar) = "cosmos.AddressString"];
  // The Misbehaviour of the consumer chain wrapping
  // two conflicting IBC headers
  ibc.lightclients.tendermint.v1.Misbehaviour misbehaviour = 2;
  // the consumer id of the consumer chain where the misbehaviour occurred
  string consumer_id = 3;
}
```

### MsgSubmitConsumerDoubleVoting

`MsgSubmitConsumerDoubleVoting` enables users to submit to the provider evidence of a double signing infraction that occured on a consumer chain. 
This message can be submitted directly by users, e.g., via the CLI command `tx provider submit-consumer-double-voting`, 
or by a relayer that can be set to automatically detect consumer chain misbehaviors, e.g., [Hermes](https://github.com/informalsystems/hermes).

Note that since the introduction of the 
[Permissionless ICS feature](https://cosmos.github.io/interchain-security/adrs/adr-019-permissionless-ics) 
the `chain_id` field is deprecated. 
Users should use `consumer_id` instead. 
You can use the `list-consumer-chains` query to get the list of all consumer chains and their consumer IDs.

For more details on reporting double signing infractions that occured on consumer chains, check out the [guide on equivocation infractions](../../features/slashing.md#equivocation-infractions).

```proto
message MsgSubmitConsumerDoubleVoting {
  option (cosmos.msg.v1.signer) = "submitter";
  option (gogoproto.equal) = false;
  option (gogoproto.goproto_getters) = false;

  string submitter = 1 [(cosmos_proto.scalar) = "cosmos.AddressString"];
  // The equivocation of the consumer chain wrapping
  // an evidence of a validator that signed two conflicting votes
  tendermint.types.DuplicateVoteEvidence duplicate_vote_evidence = 2;
  // The light client header of the infraction block
  ibc.lightclients.tendermint.v1.Header infraction_block_header = 3;
  // the consumer id of the consumer chain where the double-voting took place
  string consumer_id = 4;
}
```

## BeginBlock

In the `BeginBlock` of the provider module the following actions are performed:

- Launch every consumer chain that has a spawn time that already passed. 
  - Compute the initial validator set.
  - Create the genesis state for the consumer module. 
    Note that the genesis state contains the [consumer module parameters](./03-consumer.md#parameters) and 
    both the client state and consensus state needed for creating a provider client on the consumer chain.
  - Create a consumer client.
- Remove every stopped consumer chain for which the removal time has passed.
- Replenish the throttling meter if necessary.
- Distribute ICS rewards to the opted in validators.  

Note that for every consumer chain, the computation of its initial validator set is based on the consumer's [power shaping parameters](../../features/power-shaping.md)
and the [validators that opted in on that consumer](../../features/partial-set-security.md).

## EndBlock

In the `EndBlock` of the provider module the following actions are performed:

- Store in state the VSC id to block height mapping needed for determining the height of infractions on consumer chains.
- Prune the no-longer needed public keys assigned by validators to use when validating on consumer chains.
- Send validator updates to the consensus engine. 
  The maximum number of validators is set through the [MaxProviderConsensusValidators](#maxproviderconsensusvalidators) param.
- At the begining of every epoch, 
  - for every launched consumer chain, compute the next consumer validator set and send it to the consumer chain via an IBC packet;
  - increment the VSC id.

Note that for every consumer chain, the computation of its validator set is based on the consumer's [power shaping parameters](../../features/power-shaping.md)
and the [validators that opted in on that consumer](../../features/partial-set-security.md).

## Hooks

> TBA

## Events

> TBA

## Parameters

The provider module contains the following parameters.

### `TemplateClient`

`TemplateClient` is a template of an IBC `ClientState` used for launching consumer chains. 

### TrustingPeriodFraction

| Type   | Default value |
| ------ | ------------- |
| string | "0.66"        |

`TrustingPeriodFraction` is used to used to compute the trusting period of IBC clients 
(for both provider and consumer chains) as `UnbondingPeriod / TrustingPeriodFraction`.
Note that a light clients must be updated within the trusting period in order to avoid being frozen.

The param is set as a string, and converted to a `sdk.Dec` when used.

### CcvTimeoutPeriod

| Type          | Default value      |
| ------------- | ------------------ |
| time.Duration | 2419200s (4 weeks) |

`CcvTimeoutPeriod` is the period used to compute the timeout timestamp when sending IBC packets. 
For more details, see the [IBC specification of Channel & Packet Semantics](https://github.com/cosmos/ibc/blob/main/spec/core/ics-004-channel-and-packet-semantics/README.md#sending-packets).

:::warning
If a sent packet is not relayed within this period, then the packet times out. The CCV channel used by the interchain security protocol is closed, and the corresponding consumer is removed.
:::

`CcvTimeoutPeriod` may have different values on the provider and consumer chains.
`CcvTimeoutPeriod` on the provider **must** be larger than consumer unbonding period.

### SlashMeterReplenishPeriod

| Type          | Default value  |
| ------------- | -------------- |
| time.Duration | 3600s (1 hour) |

`SlashMeterReplenishPeriod` is the time interval at which the meter for [jail throttling](https://cosmos.github.io/interchain-security/adrs/adr-008-throttle-retries) is replenished. 
The meter is replenished to an amount equal to the allowance for that block, or `SlashMeterReplenishFraction * CurrentTotalVotingPower`.

### SlashMeterReplenishFraction

| Type   | Default value |
| ------ | ------------- |
| string | "0.05"        |

`SlashMeterReplenishFraction` is the fraction (in range `[0, 1]`) of total voting power that is replenished to the slash meter when a replenishment occurs.
This param also serves as a maximum fraction of total voting power that the slash meter can hold.

The param is set as a string, and converted to a `sdk.Dec` when used.

### ConsumerRewardDenomRegistrationFee

`ConsumerRewardDenomRegistrationFee` is deprecated. 

### BlocksPerEpoch

| Type  | Default value |
| ----- | ------------- |
| int64 | 600           |

`BlocksPerEpoch` is the number of blocks in an ICS epoch. 
The provider sends validator updates to the consumer chains only once per epoch.

:::warning
It is recommended for the length of an ICS epoch to not exceed a day. 
Large epochs would lead to delays in validator updates sent to the consumer chains, 
which might impact the security of the consumer chains. 
:::

### NumberOfEpochsToStartReceivingRewards

| Type  | Default value |
| ----- | ------------- |
| int64 | 24            |

`NumberOfEpochsToStartReceivingRewards` is the number of ICS epochs that a validator 
needs to wait after opting in on a consumer chain before being eligible to ICS reawards 
from that consumer.

### MaxProviderConsensusValidators

| Type  | Default value |
| ----- | ------------- |
| int64 | 180           |

`MaxProviderConsensusValidators` is the maximum number of validators sent to 
the provider consensus enginer. 
This was introduced with the [Inactive Provider Validators feature](https://cosmos.github.io/interchain-security/adrs/adr-017-allowing-inactive-validators) 
and it replaces the `MaxValidators` staking module parameter.  
As a result, the provider chain can differentiate between 
_bonded validators_, i.e., validators that have stake locked on the provider chain, 
and _active validator_, i.e., validators that participate actively in the provider chain's consensus. 

## Client

### CLI

### gRPC

### REST