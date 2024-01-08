---
sidebar_position: 15
title: Epochs
---
# ADR 014: Epochs

## Changelog
* 2024-01-105: Proposed, first draft of ADR.

## Status

Proposed

## Context

In every block that the provider valset changes, a `VSCPacket` must be sent to every consumer and a corresponding `VSCMaturedPacket` sent back.
Given that the validator powers may change very often on the provider chain (e.g., the Cosmos Hub), this approach results in a large workload for the relayers. 
Although the validator powers may change very often, these changes are usually small and have an insignificant impact on the chain's security.
In other words, the valset on the consumers can be slightly outdated without affecting security. 
As a matter of fact, this already happens due to relaying delays. 

As a solution, this ADR introduces the concept of _epochs_. 
An epoch consists of multiple blocks. 
The provider sends `VSCPacket`s once per epoch. 
A `VSCPacket` contains all the valset changes that occurred throughout the epoch. 

## Decision

The implementation of epochs requires the following changes:

- Add a param that sets the number of blocks in an epoch, i.e., `BlocksPerEpoch`. 
  We can use `BlockHeight() % BlocksPerEpoch == 0` to decide when an epoch is over. 
  Note that `BlocksPerEpoch` can also be a hardcoded constant as it's unlikely that it will change often.
- In every provider `EndBlock()`, instead of queueing `VSCPacket` data for every consumer chain, we accumulate the validator changes (similarly to how is done on the consumer, see `AccumulateChanges`). 
- Modify the key assignment logic to allow for `MustApplyKeyAssignmentToValUpdates` to be called once per epoch. 
  Currently, this method is called in every block before queueing a `VSCPacket`. 
  Also, the method uses the `KeyAssignmentReplacement` state, which is pruned at the end of every block. 
  This needs to be done once per epoch instead.
- At the end of every epoch, if there were validator set changes on the provider, then for every consumer chain, construct a `VSCPacket` with all the accumulated validator changes and add it to the list of `PendingVSCPackets`.

As an optional change, to better accommodate [the Partial Set Security design](https://informalsystems.notion.site/Partial-Set-Security-398ca9a1453740068be5c7964a4059bb), the validator changes should be accumulated per consumer chain. 
Like this, it would make it easier to have validators opting out from certain consumer chains. 

## Consequences

### Positive

- Reduce the cost of relaying.
- Reduce the amount of IBC packets needed for ICS.

### Negative

- Additional logic on the provider side as valset changes need to be accumulated. 
- The changes might impact the key-assignment logic so special care is needed to avoid introducing bugs.

### Neutral

N/A

## References

* [EPIC](https://github.com/cosmos/interchain-security/issues/1087)
