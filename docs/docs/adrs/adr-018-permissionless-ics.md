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

This ADR presents _Permissionless_ ICS, a way in which an [_Opt In_](adr-015-partial-set-security.md) consumer chain can join
ICS without needing a governance proposal but by simply issuing a transaction.

## Decision

### The phases of a consumer chain
In Permissionless ICS, launching an Opt In chain is **only** possible through a transaction and not through a `ConsumerAdditionProposal`.
Nevertheless, Permissionless ICS does not eliminate the `ConsumerAdditionProposal` governance proposal, as proposals are still necessary
for Top N chains. Because of this, this ADR outlines a solution that attempts to preserve as much of the governance proposal code
as possible. In what follows, what we describe applies to both governance-proposed consumer (i.e., Top N) chains and transaction-based (i.e., Opt In) chains.

A consumer chain can reside in three phases: i) _prelaunch_, ii) _launched_, and iii) _stopped_ phase as seen
in the diagram below:
![Phases of a consumer chain](./adr18_phases_of_a_consumer_chain.png)

When a Top N chain is first proposed through a `ConsumerAdditionProposal` or an Opt In chan is added through a transaction,
the consumer chain resides in the _prelaunch_ phase. At this state, validators can choose to opt in on the consumer chain. Additionally,
an Opt In chain can choose to change parameters of the to-be-launched chains, such as `spawnTime`, etc. by issuing a specific transaction.
This is not the case for Top N chains, where a `ConsumerModificationProposal` can only be issued after a consumer
chain [has started](https://github.com/cosmos/interchain-security/blob/v4.3.0/x/ccv/provider/keeper/proposal.go#L150).

When the [`spawnTime`](https://github.com/cosmos/interchain-security/blob/v4.3.0/proto/interchain_security/ccv/provider/v1/provider.proto#L55)
passes and [at least one validator has opted in](https://github.com/cosmos/interchain-security/blob/v4.3.0/x/ccv/provider/keeper/proposal.go#L455)
the chain can launch and moves to the _launched_ phase. While in launched phase, a Top N consumer chain can choose to modify
its parameters through a `ConsumerModificationProposal` and an Opt In chain can change its parameters by issuing a transaction.

Lastly, a Top N chain can choose to exit ICS by issuing a `ConsumerRemovalProposal` and an Opt In chain can issue a transaction to stop the chain.
After some period of time (e.g., provider's unbonding period), all state related to the stopped consumer chain can be removed. We need
to keep track of the consumer chain's state for some period, so that we are able to punish validators for misbehaviour.

Note that everything described so far and everything that follows applies to standalone chains as well that join ICS.

### From `chainID` to `consumerID`
A hindrance in moving to Permissionless ICS is chain-id squatting. In a permissionless setting, anyone could issue a transaction
to launch a consumer chain with a `chainID` that might already be used by some other consumer chain. This is a problem
because in the current design the majority of stored state for a consumer chain is indexed using the `chainID` as the key (e.g.,
see [key used to store client ids](https://github.com/cosmos/interchain-security/blob/v4.3.0/x/ccv/provider/types/keys.go#L233)).
To tackle this problem, in Permissionless ICS, we introduce the `consumerID` that defines a consumer chain and is simply
a combination of a `chainID` and an increasing sequence number, thus we can support multiple consumer chains with the same `chainID`.
Nevertheless, as a result of using `consumerID`, we have to migrate a substantial chunk of state to re-index it using `consumerID` as the key.

#### State
To do move from a `consumerID` to a `chainID`, we need to revamp the consumer chains' stored state in ICS. Currently, in
ICS we have state that is indexed by a multitude of [keys](https://github.com/cosmos/interchain-security/blob/v4.3.0/x/ccv/provider/types/keys.go#L40).
In the table below, we see which ones are associated with a `chainID` and how often state under those keys gets updated.

| Key                                     |Description                                                                       |Associated with `chainID`?|How often are `chainID`-associated keys updated?                          |
|-----------------------------------------|----------------------------------------------------------------------------------|--------------------------|--------------------------------------------------------------------------|
| `PortByteKey`                           |Global `portID`                                                                   |NO                        |                                                                          |
| `MaturedUnbondingOpsByteKey`            |Deprecated together with `VSCMaturedPacket`s                                      |-                         |                                                                          |
| `ValidatorSetUpdateIdByteKey`           |Global for all consumer chains                                                    |NO                        |                                                                          |
| `SlashMeterByteKey`                     |Global for the provider                                                           |NO                        |                                                                          |
| `SlashMeterReplenishTimeCandidateByteKey`|Global for the provider                                                           |NO                        |                                                                          |
| `ChainToChannelBytePrefix`              |Stores the CCV `channelID` for a specific chain                                   |**YES**                   |Only once (during set up)                                                 |
| `ChannelToChainBytePrefix`              |Stores `chainID` for a specific channel                                           |**YES**                   |Only once (during set up)                                                 |
| `ChainToClientBytePrefix`                |Stores the `clientID` for a specific chain                                        |**YES**                   |Only once (during set up)                                                 |
| `InitTimeoutTimestampBytePrefix`         |Deprecated together with `VSCMaturedPacket`s                                      |-                         |                                                                          |
| `PendingCAPBytePrefix`                   |Stores pending consumer addition proposals                                        |**YES**                   |Only once (for successful proposal)                                       |
| `PendingCRPBytePrefix`                   |Stores pending consumer removal proposals                                         |**YES**                   |Only once (for successful proposal)                                       |
| `UnbondingOpBytePrefix`                  |Deprecated together with `VSCMaturedPacket`s                                      |-                         |                                                                          |
| `UnbondingOpIndexBytePrefix`             |Deprecated together with `VSCMaturedPacket`s                                      |-                         |                                                                          |
| `ValsetUpdateBlockHeightBytePrefix`      |Not needed anymore. Used to keep track of the infraction height.                  |NO                        |                                                                          |
| `ConsumerGenesisBytePrefix`              |Stores the consumer genesis for a specific chain                                  |**YES**                   |Only once (during set up)                                                 |
| `SlashAcksBytePrefix`                    |Stores slash acks for a specific consumer chain                                   |**YES**                   |Every time we receive a Slash packet                                      |
| `InitChainHeightBytePrefix`              |Not needed anymore. Used to keep track of the infraction height.                  |-                         |                                                                          |
| `PendingVSCsBytePrefix`                  |Stores `VSCPacket`s for a specific consumer chian                                 |**YES**                   |Every epoch                                                               |
| `VscSendTimestampBytePrefix`             |Deprecated together with `VSCMaturedPacket`s                                      |-                         |                                                                          |
| `ThrottledPacketDataSizeBytePrefix`      |Deprecated                                                                        |-                         |                                                                          |
| `ThrottledPacketDataBytePrefix`          |Deprecated                                                                        |-                         |                                                                          |
| `GlobalSlashEntryBytePrefix`             |Deprecated                                                                        |-                         |                                                                          |
| `ConsumerValidatorsBytePrefix`           |Stores consumer key per validator per consumer chain                              |**YES**                   |Every `MsgAssignConsumerKey` or `MsgOptIn`                                |
| `ValidatorsByConsumerAddrBytePrefix`     |Stores consumer to provider validator address                                     |**YES**                   |Every `MsgAssignConsumerKey` or `MsgOptIn`                                |
| `KeyAssignmentReplacementsBytePrefix`    |Deprecated                                                                        |-                         |                                                                          |
| `ConsumerAddrsToPruneBytePrefix`         |Deprecated together with `VSCMaturedPacket`s                                      |-                         |                                                                          |
| `SlashLogBytePrefix`                     |Not used                                                                          |-                         |                                                                          |
| `ConsumerRewardDenomsBytePrefix`         |Global for all consumer chains                                                    |NO                        |                                                                          |
| `VSCMaturedHandledThisBlockBytePrefix`   |Deprecated together with `VSCMaturedPacket`s                                      |-                         |                                                                          |
| `EquivocationEvidenceMinHeightBytePrefix` |Stores min height for a consumer chain                                            |**YES**                   |Only once (during set up)                                                 |
| `ProposedConsumerChainByteKey`           |Stores `proposalID` for a specific chain                                          |**YES**                   |                                                                          |
| `ConsumerValidatorBytePrefix`            |Stores consumer validators for a specific chain                                   |**YES**                   |Potentially at every [epoch](ADR on epochs)                               |
| `OptedInBytePrefix`                      |Stores opted-in validators for a specific chain                                   |**YES**                   |Potentially at every block                                                |
| `TopNBytePrefix`                         |Stores whether a consumer chain is Top N or not                                   |**YES**                   |Every parameter update                                                    |
| `ValidatorsPowerCapPrefix`               |Stores ther power cap of a chain                                                  |**YES**                   |Every parameter update                                                    |
| `ValidatorSetCapPrefix`                  |Stores the set cap of a chain                                                     |**YES**                   |Every parameter update                                                    |
| `AllowlistPrefix`                        |Stores the allowlist of a chain                                                   |**YES**                   |Every parameter update                                                    |
| `DenylistPrefix`                         |Stores the denylist of a chain                                                    |**YES**                   |Every parameter update                                                    |
| `ConsumerRewardsAllocationBytePrefix`    |Stores the ICS rewards per chain                                                  |**YES**                   |Every IBC transfer packet that sends rewards to the provider              |
| `ConsumerCommissionRatePrefix`           |Comission rate per chain per validator                                            |**YES**                   |Every `MsgSetConsumerCommissionRate` message                              |
| `MinimumPowerInTopNBytePrefix`           |Stores the minimum power needed to opt in for a chain                             |**YES**                   |Every epoch                                                               |
| `ConsumerAddrsToPruneV2BytePrefix`       |Stores consumer addresses to be pruned (as part of `VSCMaturedPacket`s deprecation)|**YES**                   |Every `MsgAssignConsumerKey` or `MsgOptIn` and later during actual pruning|

Everything stored under a key associated with a `chainID` needs to be migrated to new state under `consumerID`. 
Because we have to migrate in any case, we can also clean up a number of those keys by building a `ConsumerChainRecord` while
we are it. The `ConsumerChainRecord` contains state relevant to a consumer chain and is keyed by a `consumerID`. Although the `ConsumerChainRecord`
could contain **all** state related to a consumer chain (e.g., opted-in and consumer validators of a chain) we do not include
such fields in the `ConsumerChainRecord` because this would increase the cost of ICS-related transactions due to the [gas cost](https://github.com/cosmos/cosmos-sdk/blob/v0.50.7/store/gaskv/store.go#L40).
Furthermore, if we were to store all the opted-in or consumer validators, etc. it would be tricky to read or write those fields,
because we would need to extract the opted-in validators from the `ConsumerChainRecord` and then search through those
validators to find the one we are looking for, etc.

The `ConsumerChainRecord` is going to be:
```protobuf
message ConsumerChainRecord {
  // the owner of this consumer chain
  string owner_address;
  // client id to the consumer chain
  string client_id;
  // channel id
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
to the address that issued the `MsgLaunchConsumerChain` (see later). The `owner_address` can be updated by issuing a `MsgUpdateConsumerChain` (see later).
Note that we create a `ConsumerChainRecord` at the _launched_ phase of a consumer chain.

### New Messages
In what follows, we describe the new messages that Permissionless ICS introduces and on how those can be used.
We then, describe how we can utilize those messages with our existing codebase.

#### Launch a Consumer Chain
To prepare a consumer chain for launch, we issue a `MsgLaunchConsumerChain` message that is as follows:

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

We intend to set a fixed cost of a `MsgLaunchConsumerChain` to avoid getting spammed with bogus consumer launch chains.

To execute a `MsgLaunchConsumerChain`, we first create a `ConsumerAdditionProposal` under the hoods, with the `top_N` set to 0, and call
[`HandleConsumerAdditionProposal`](https://github.com/cosmos/interchain-security/blob/v4.3.0/x/ccv/provider/keeper/proposal.go#L30)
as if the proposal was already voted on and accepted. Note that we need to migrate `ConsumerAdditionProposal`s to use
based on the `consumerID` instead using [both](https://github.com/cosmos/interchain-security/blob/v4.3.0/x/ccv/provider/keeper/proposal.go#L382)
`chainID` and the `spawnTime` as keys. The [usual validity conditions]((https://github.com/cosmos/interchain-security/blob/v4.3.0/x/ccv/provider/types/proposal.go#L114))
hold for the fields of the `MsgLaunchConsumerChain`. Note however, that we intend to have a `spawnTime` upper limit as well.
For example, if you launch a consumer chain in Permissionless ICS, the `spawnTime` should not be more
than two months ahead in the future, to avoid having consumer chains lingering for too long before they get added. To do this,
we intend to introduce a `maxSpawnTime` limit in [`ConsumerAdditionProposal`](https://github.com/cosmos/interchain-security/blob/v4.3.0/proto/interchain_security/ccv/provider/v1/provider.proto#L29).
This way, Opt In consumer chains that reach their `spawnTime` but have no validator opted in, get simply removed.

#### Modify a Consumer Chain

We introduce the `MsgUpdateConsumerChain` message so that the owner of a consumer chain can change its parameters
(e.g., `spawn_time`, PSS-related parameters, etc.) This message can only be executed by the owner of a consumer chain (see `owner_address` in the `ConsumerChainRecord`).

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
is still in the prelaunch phase. This can be achieved by looking if there's an ongoing consumer addition proposal for this `consumerID`,
and going and changing the fields of ths proposal. The other fields such as `allowlist`, etc. can be changed at any point before or after a chain has started.

#### Stop a Consumer Chain
With the `MsgStopConsumerChain` we can stop any Opt In chain at any moment. Note that all relevant state for this consumer chain
remains on the provider's state before getting removed for the provider's unbonding period. This is to enable
potential slashing for any infraction that might have been caused until now. After the unbonding period, the `ConsumerChainRecord`
associated with this chain is removed. Note however that `consumerID`s are **never** reused. Naturally, this message
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
we only have two consumer chains at the moment, this is not going to be an expensive migration even if we have some
consumer chains that are being voted upon. Similarly, all the messages, queries, etc. would need to be changed to operate on a `consumerID`
instead of a `chainID`.

### Garbage collect

## Consequences

### Positive
- Easier to launch an Opt In consumer chain because no governance is required.

### Negative 

### Neutral 

## References
[CHIPs Discussion phase: Permissionless ICS](https://forum.cosmos.network/t/chips-discussion-phase-permissionless-ics/13955)