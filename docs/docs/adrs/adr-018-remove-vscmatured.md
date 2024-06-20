---
sidebar_position: 19
title: Remove VSCMatured Packets
---
# ADR 018: Remove VSCMatured Packets

## Changelog
* 19/06/2024: Create initial draft

## Status

Proposed

## Context

The consumer module on the consumer chains is a representation of the Hub’s staking module, i.e., it provides an _asynchronous_ view of the voting powers and indirectly of the locked collateral. 
The key word here is _asynchronous_, which means that (in theory) there is no bound on the lag between the Hub’s view of stake and the consumer’s view of stake. 
The reasons for this asynchrony are relaying delays and chain liveness (e.g., a consumer could be down for a long period of time without affecting the liveness of the staking module on the Hub). 

The current version of ICS uses `VSCMaturedPackets` to create on the consumers a _partially synchronous_ view of the Hub’s staking module. 
Partially synchronous means that the lag between the Hub’s view of stake and the consumer’s view of stake is bounded. 
Basically, unlocking collateral from the Hub is being delayed until the consumers’ `UnbondingPeriod` elapses. 
The reason the view is only partially synchronous is that eventually the collateral is unlocked, i.e., if `VSCMaturedPackets` are not received from a consumer for `VscTimeoutPeriod` (default: 5 weeks), then the consumer is removed from ICS and the collateral is unlocked. 
Note that keeping the stake locked “forever” would affect the Hub’s liveness, so it’s not a viable option. 

The issue is that whatever attack is possible with an asynchronous view of the staking module, it is eventually possible with the partially synchronous view as well. 
For example, an attacker could wait for `VscTimeoutPeriod` for the collateral to be unlocked and then send invalid headers to third-party chains that are not aware the consumer's collateral is no longer locked on the Hub (i.e., the consumer is no longer part of ICS). 

Moreover, with the introduction of [PSS](./adr-015-partial-set-security.md), a consumer’s validator set could “lie” about its `UnbondingPeriod` elapsing by sending `VSCMaturedPackets` earlier. 
This would result in a discrepancy between a light client’s view of the `UnbondingPeriod` and the actual Hub’s `UnbondingPeriod`.

## Decision

This ADR proposes the removal of `VSCMaturedPackets`. The reason is twofold. 
First, `VSCMaturedPackets` provide a "false" sense of correctness as the attack discribed above is still possible.
Second, `VSCMaturedPackets` add considerable complexity to the ICS protocol -- an extra message plus the pausing of unbonding operations that can affect the UX.

To simplify the upgrading process, removing `VSCMaturedPackets` can be done in two releases:

* (R1) Update the provider to drop `VSCMaturedPackets`. 
* (R2) Update the consumer to stop sending `VSCMaturedPackets`. 

As a result, once the provider chain runs R1, the consumers can start upgrading to R2.

### Provider Changes (R1)

#### Parameters

Deprecate the `VscTimeoutPeriod` parameter. 

#### State

Remove the following key prefixes from the state:

- `MaturedUnbondingOpsByteKey` -- the byte key that stores the list of all unbonding operations ids that have matured from a consumer chain perspective.
- `UnbondingOpBytePrefix` -- the byte prefix that stores a record of all the ids of consumer chains that need to unbond before a given unbonding operation can unbond on this chain.
- `UnbondingOpIndexBytePrefix` -- the byte prefix of the index for looking up which unbonding operations are waiting for a given consumer chain to unbond.
- `VscSendTimestampBytePrefix` -- the byte prefix for storing the list of VSC sending timestamps for a given consumer chainID.

Note that these removals require state migration. 

#### State Transitions

Removing `VSCMaturedPackets` affects three ICS sub-protocols (see [HandleVSCMaturedPacket](https://github.com/cosmos/interchain-security/blob/v4.2.0/x/ccv/provider/keeper/relay.go#L51)): unbonding operations pausing, `VSCPackets` timeout, and key assignment pruning. 
The first two are no longer needed, while the third (key assignment pruning) needs to be redesigned to not depend on `VSCMaturedPackets`. 

**Removing unbonding operations pausing:** 

- Make the `AfterUnbondingInitiated` hook a no-op. As a result, unbonding operations are no longer paused. 
- Stop calling the `UnbondingCanComplete` method from the staking keeper. This entails, it is no longer necessary to append `MaturedUnbondingOps` and the `completeMaturedUnbondingOps` method can be removed. 
- Note, that during the upgrade, all unbonding operations stored under the `UnbondingOpBytePrefix` prefix need to be completed (via the `UnbondingCanComplete` method from the staking keeper). 

**Removing `VSCPackets` timeout:**

- Stop setting VSC send timestamps when sending `VSCPackets`.
- Stop removing the VSC send timestamps when receiving `VSCMaturedPackets`.
- Remove the logic from `EndBlockCCR` that checks if the first VSC send timestamp in iterator plus `VscTimeoutPeriod` exceeds the current block time.
- Deprecate the `VscTimeoutPeriod` parameter. 

**Redesign key assignment pruning.** The reason for keeping "old" consumer addresses in the previous design was to enable slashing / jailing validators that misbehave on consumer chains, 
i.e., the slashing logic uses the `GetProviderAddrFromConsumerAddr` method that accesses the mapping from validator addresses on consumer chains to validator addresses on the provider chain (`ValidatorsByConsumerAddrBytePrefix`).
Thus, "old" consumer addresses are no longer needed after the provider's `UnbondingPeriod` elapses. 
This means that once a validator changes its key on a consumer, we can prune the address corresponding to the "old" key after `UnbondingPeriod`. 
This requires the following changes:

- Add a new prefix (i.e., `ConsumerAddrsToPruneV2BytePrefix`) to store consumer addresses that need to be pruned under a key with the format `bytePrefix | len(chainID) | chainID | timestamp` (see `ChainIdAndTsKey`).
- Adapt the `AppendConsumerAddrsToPrune()` method to use the timestamp of the current block instead of the current `vscID`.
- Add a new method `PruneKeyAssignmentsV2()` that adapts `PruneKeyAssignments()` to take a timestamp as an argument and iterate over `ConsumerAddrsToPruneV2BytePrefix`.
- Call the `PruneKeyAssignmentsV2()` method in every `EndBlock` instead of calling `PruneKeyAssignments()` in `HandleVSCMaturedPacket`. 

Note that the existing "old" consumer addresses stored under the `ConsumerAddrsToPruneBytePrefix` need to be pruned eventually to avoid slashing validator for "old" misbehaviors. 
As a result, `PruneKeyAssignments()` needs to be called for `UnbondingPeriod` (i.e., three weeks). 
Once the `UnbondingPeriod` elapses, the consumers can be upgraded to stop sending `VSCMaturedPackets` (see [R2](#consumer-changes-r2) below) and the provider can be upgraded to stop calling `PruneKeyAssignments()` (and all the data under `ConsumerAddrsToPruneBytePrefix` can be removed).

#### Queries

Remove the `oldest_unconfirmed_vsc` query. 

### Consumer Changes (R2)

#### Parameters

Given that currently relayers use the consumer `UnbondingPeriod` (see `ConsumerParams`), this param cannot be deprecated. 
The `UnbondingTime` method from the staking interface will continue to be used to retrieve the consumer's `UnbondingPeriod`.

#### State

Remove the following key prefixes from the state:

- `PacketMaturityTimeBytePrefix` -- the byte prefix that will store maturity time for each received VSC packet

Note that these removals require state migration. 

#### State Transitions

To stop the consumer chains from sending `VSCMaturedPackets`, it is sufficient to not store the maturity time of `VSCPacket`s when receiving them, i.e., do not call `SetPacketMaturityTime` from the `OnRecvVSCPacket()` method. 
Note that eventually, no additional `VSCMaturedPackets` will be added to the sending queue as `QueueVSCMaturedPackets` iterates over elapsed maturity times. 
In addition, to cleanup the code, the `QueueVSCMaturedPackets` must be removed. 

#### Messages

`VSCMaturedPacketData` is deprecated. 
Note that this is a wire-breaking change -- older consumer versions will send `VSCMaturedPackets` and older provider versions will expect to receive `VSCMaturedPackets`. 

## Consequences

### Positive

- Remove feature that provides a "false" sense of correctness.
- Remove unnecessary complexity, from both ICS and Cosmos SDK. 
- Remove one IBC packet and, thus, reduce relaying cost. 
- Remove unbonding pausing logic that could affect the UX.

### Negative

- Large refactor that might introduce unexpected bugs. 

### Neutral

- Consumer chains are no longer removed after a `VscTimeoutPeriod` of inactivity. 
  Note that consumers are still removed if their CCV channel expires, which usually happens after two weeks instead of five weeks (the default value for `VscTimeoutPeriod`). 

## References


