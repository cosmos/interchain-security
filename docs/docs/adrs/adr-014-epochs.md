---
sidebar_position: 15
title: Epochs
---
# ADR 014: Epochs

## Changelog
* 2024-01-05: Proposed, first draft of ADR.
* 2024-02-29: Updated so that it describes the implementation where we store the whole consumer validator set.

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
A `VSCPacket` contains all the validator updates that are needed by consumer chains.

## Decision

The implementation of epochs requires the following changes:

- For each consumer chain, we store the consumer validator set that is currently (i.e., in this epoch) validating the 
  consumer chain. For each validator in the set we store i) its voting power, and ii) the public key that it is 
  using on the consumer chain during the current (i.e., ongoing) epoch.
  The initial consumer validator set for a chain is set during the creation of the consumer genesis.  
- We introduce the `BlocksPerEpoch` param that sets the number of blocks in an epoch. By default, `BlocksPerEpoch` is
  set to be 600 which corresponds to 1 hour, assuming 6 seconds per block. This param can be changed through
  a _governance proposal_ to be anywhere between `[1, MaxBlocksPerEpoch]` where `MaxBlocksPerEpoch` can be up to 1200
  (2 hours if we assume 6 seconds per block). In the provider `EndBlock` we check `BlockHeight() % BlocksPerEpoch() == 0`
  to decide when an epoch has ended.
- At the end of every epoch, if there were validator set changes on the provider, then for every consumer chain, we 
  construct a `VSCPacket` with all the validator updates and add it to the list of `PendingVSCPackets`. We compute the
  validator updates needed by a consumer chain by comparing the stored list of consumer validators with the current
  bonded validators on the provider, with something similar to this:
```go
// get the valset that has been validating the consumer chain during this epoch 
currentValidators := GetConsumerValSet(consumerChain)
// generate the validator updates needed to be sent through a `VSCPacket` by comparing the current validators 
// in the epoch with the latest bonded validators
valUpdates := DiffValidators(currentValidators, stakingmodule.GetBondedValidators())
// update the current validators set for the upcoming epoch to be the latest bonded validators instead
SetConsumerValSet(stakingmodule.GetBondedValidators())
```
Note that a validator can change its consumer public key for a specific consumer chain an arbitrary amount of times during
a block and during an epoch. Then, when we generate the validator updates in `DiffValidators`, we have to check on whether
the current consumer public key (retrieved by calling `GetValidatorConsumerPubKey`) is different from the consumer public
key the validator was using in the current epoch.

## Consequences

### Positive

- Reduce the cost of relaying.
- Reduce the amount of IBC packets needed for ICS.
- Simplifies [key-assignment code](https://github.com/cosmos/interchain-security/blob/main/docs/docs/adrs/adr-001-key-assignment.md) because
  we only need to check if the `consumer_public_key` has been modified since the last epoch to generate an update. 

### Negative

- Increase the delay in the propagation of validator set changes (but for reasonable epoch lengths on the order of ~hours or less, this is unlikely to be significant).

### Neutral

N/A

## References

* [EPIC](https://github.com/cosmos/interchain-security/issues/1087)
