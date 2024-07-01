---
sidebar_position: 19
title: Permissionless ICS
---
# ADR 18: Permissionless Interchain Security

## Changelog
* 27th of June, 2024: Initial draft

## Status

Proposed

## Context
Currently, a consumer chain can join _Interchain Security_ (ICS) only through a [governance proposal](../features/proposals.md).
A governance proposal was needed before the introduction of [Partial Set Security](../features/partial-set-security.md) (PSS)
because validators were required to validate a consumer chain. However, after the introduction of PSS, a consumer chain can
be either _Top N_ or _Opt In_. If a chain is an Opt In chain, then no validator is required to validate this chain unless they choose to.
Because of this, we can launch an Opt In consumer chain without going through a governance proposal.

This ADR presents _Permissionless_ ICS, a way in which [_Opt In_](adr-015-partial-set-security.md) a consumer chain can join
ICS without having to go through a governance proposal but by simply issuing a transaction.
Note that this ADR does not eliminate the `ConsumerAdditionProposal` governance proposal because consumer chains might
choose to be Top N chains and in this case, governance proposals are still necessary.

## Decision
In what follows, we describe the new messages that Permissionless ICS introduces and on how those can be used.
We then, describe how we can utilize those messages with our existing codebase.

### New Messages

#### Launch a Consumer Chain 
To launch a consumer chain, we issue a `MsgLaunchConsumerChain` message that is as follows:

```protobuf
message MsgLaunchConsumerChain {
  // the title of this launch 
  string title;
  // the description of this consumer chain
  string description;
  // the chain-id of the new consumer chain
  string chain_id;
  // the proposed initial height of new consumer chain.
  ibc.core.client.v1.Height initial_height;

  ...  (all fields contained in ConsumerAdditionProposal except top_N)
  
  uint32 validators_power_cap;
  uint32 validator_set_cap;
  repeated string allowlist;
  repeated string denylist;
}
```

The cost of the `MsgLaunchConsumerChain` message is the same as that of issuing a `ConsumerAdditionProposal` governance proposal
(i.e., 250 ATOMs).

`MsgLaunchConsumerChain` contains everything that is contained in [`ConsumerAdditionProposal`](https://github.com/cosmos/interchain-security/blob/v4.3.0/proto/interchain_security/ccv/provider/v1/provider.proto#L29)
except the `top_N` field because we can only launch Opt In consumer chains with this message (Top N chains still need to go
through a governance proposal). Note, that an alternative format for this message could have been to include a single `ConsumerAdditionProposal` field in it,
but this confuses the semantics of `MsgLaunchConsumerChain` and that of a governance proposal. The response of this message
(i.e., `MsgLaunchConsumerChainResponse`) contains a single `string` named `consumerID`. The `consumerID`s corresponds
to `len(chainID) | chainID | counter` and this way we can have multiple different `consumerID`s that correspond to a chain
with the same `chainID`. By doing this, we tackle the main issue behind permissionless consumer chains that is chain-id squatting.
Note that `consumerID` could just be a `uint64` but we choose to include `chainID` in it as well so that it is easier to see
what the consumer chain just by looking at the `consumerID`. This means that the `chainID` of a chain cannot be changed
after launching it (because the `chainID` is part of the `consumerID` key).

When we execute a `MsgLaunchConsumerChain`, we first create a `ConsumerAdditionProposal` under the hoods, with the `top_N` set to 0, and call
[`HandleConsumerAdditionProposal`](https://github.com/cosmos/interchain-security/blob/v4.3.0/x/ccv/provider/keeper/proposal.go#L30)
as if the proposal was already voted on and accepted. Note that we need to migrate `ConsumerAdditionProposal`s to use
based on the `consumerID` instead using [both](https://github.com/cosmos/interchain-security/blob/v4.3.0/x/ccv/provider/keeper/proposal.go#L382)
`chainID` and the `spawnTime` as keys.

The [usual validity conditions]((https://github.com/cosmos/interchain-security/blob/v4.3.0/x/ccv/provider/types/proposal.go#L114))
hold for the fields of the `MsgLaunchConsumerChain`. Note however, that intend to have a `spawnTime` upper limit as well.
For instance, if you launch a consumer chain permissionlessly, the `spawnTime` should not be more
than one month ahead in the future, to avoid having consumer chains lingering for too long before they get added.

When executing the `MsgLaunchConsumerChain`, we also generate a `ConsumerChainRecord` that includes relevant information
for this consumer chain again using as a key the `consumerID`. A `ConsumerChainRecord` contains:
```protobuf
message ConsumerChainRecord {
  // the owner of this consumer chain
  string owner_address;
  // client id to the consumer chain (empty for a not-started chain)
  string client_id;
  // channel id (empty for a not-started chain)
  string channel_id;
  // the chain-id of the consumer chain
  string chain_id;
  // min height needed for an equivocation to be actionable
  uint64 equivocation_evidence_min_height;
  // maximum power (percentage-wise) a validator can have on the consumer chain
  uint32 validators_power_cap;
  // maximum number of validators that can validate a consumer chain
  uint32 validator_set_cap;
  // allowlist of provider consensus addresses of validators that are the ONLY ones that can validate the consumer chain
  repeated string allowlist;
  // denylist of provider consensus addresses of validators that are the CANNOT validate the consumer chain
  repeated string denylist;
}
```
We store the `ConsumerChainRecord`s using the `consumerID` as their key. The `owner_address` of a consumer chain corresponds
to the address that issued the `MsgLaunchConsumerChain`. The `owner_address` can be updated by issuing a `MsgUpdateConsumerChain` (see below). 
Note that we create a `ConsumerChainRecord` when a `ConsumerAdditionProposal` goes through a normal governance proposal as well.

The `ConsumerChainRecord` is a long-lived object that contains some fields
relevant to a consumer chain that are to be used frequently. In this sense, it is not constructive to include fields such as `spawnTime`, `initialHeight`,
`binaryHash`, etc. because those fields are only used during the consumer's addition.
Additionally, there are multiple other fields that we currently have that are associated with a consumer chain, such as opted-in
validators, consumer validators, etc. However, we do not include such fields in the `ConsumerChainRecord` because this would increase
the cost of ICS-related transactions due to the increased [gas cost](https://github.com/cosmos/cosmos-sdk/blob/v0.50.7/store/gaskv/store.go#L40).
Furthermore, if we were to store all the opted-in or consumer validators, etc. it would be more tricky to read those,
because we would need to extract the `ConsumerChainRecord` and then the slice of consumer validators from it, etc. and
then perform a search on it.

#### Modify a Consumer Chain

We introduce the `MsgUpdateConsumerChain` message so that the owner of a potentially not-yet started consumer chain can
change its parameters (e.g., `spawn_time`, PSS-related parameters, etc.)
This message can only be executed by the owner of a consumer chain (see `owner_address` in the `ConsumerChainRecord`).

```protobuf
message MsgUpdateConsumerChain {
  // for which chain to change the state ...
  string consumer_id;

  // if the user intends to change the owner_address
  // the one issuing this message should be able to sign this message as well?
  string owner_address;
  
  // the chain-id of the new consumer chain
  string chain_id;
  // the proposed initial height of new consumer chain.
  ibc.core.client.v1.Height initial_height;

  ...  (all fields contained in ConsumerAdditionProposal except top_N)
  
  uint32 validators_power_cap;
  uint32 validator_set_cap;
  repeated string allowlist;
  repeated string denylist;
}
```

The `owner_address` is provided as well and hence a validator can change this as can be seen.

The `initial_height`, `spawnTime` and everything else could be provided here but would only be applicable if the chain
has not yet started. This is done by looking if there's an ongoing consumer addition proposal for this `consumerID`.
The other fields such as `allowlist`, etc. can be changed at any point before or after a chain has started.

#### Stop a Consumer Chain
With the `MsgStopConsumerChain` we can stop any Opt In chain at any moment. Note that all relevant state for this chain
would remain on the provider's state before getting removed for the provider's unbonding period. This is to enable
potential slashing for any infraction that might have been caused until now. After the unbonding period, the `ConsumerChainRecord`
associated with this chain is removed. Note however that `consumerID`s are never reused. Naturally, this message
can only be issued by the owner of the consumer chain.

```protobuf
message MsgStopConsumerChain {
  // the consumerID as returned by `MsgLaunchConsumerChain`
  string consumer_id;
}
```

### Migration
We need to perform multiple migrations at this moment. One is for the `ConsumerAdditionProposal`, etc. and the other
to generate the `ConsumerChainRecord`s for the existing consumer chains, as well as deleting the old keys. Because
we only have two consumer chains at the moment, this does not seem such an expensive migration even if we have some
consumer chains that are being voted upon. We would also need to migrate all opted-in validators, consumer validators, etc.
to operate on `consumerID`s instead of simply on a `chainID`. Similarly all the messages, queries, etc. would need
to operate on a `consumerID`.

### Garbage collect
Having lingering `ConsumerChainRecord`s, etc. does not seem a problem per se at this moment if the cost of launching
a chain is 250 ATOMs.

## Consequences

### Positive
- Much easier to launch a consumer chain, without having to go through governance.

### Negative 

### Neutral 

## References
[CHIPs Discussion phase: Permissionless ICS](https://forum.cosmos.network/t/chips-discussion-phase-permissionless-ics/13955)