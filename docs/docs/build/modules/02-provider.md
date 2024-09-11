---
sidebar_position: 2
---

# x/provider

## Overview

## State 

## State Transitions

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

## Begin-Block

## End-Block

## Hooks

## Events

## Parameters

## Client