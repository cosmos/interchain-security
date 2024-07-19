---
sidebar_position: 3
title: Key Assignment
---

# ADR 001: Key Assignment

## Changelog
* 2022-12-01: Initial Draft
* 2024-03-01: Updated to take into account they key-assigment-replacement deprecation.

## Status

Accepted

## Context

KeyAssignment is the name of the feature that allows validator operators to use different consensus keys for each consumer chain validator node that they operate.

## Decision

It is possible to change the keys at any time by submitting a transaction (i.e., `MsgAssignConsumerKey`).

### State required

- `ValidatorConsumerPubKey` - Stores the validator assigned keys for every consumer chain.
```golang
ConsumerValidatorsBytePrefix | len(chainID) | chainID | providerConsAddress -> consumerKey
```
- `ValidatorByConsumerAddr` - Stores the mapping from validator addresses on consumer chains to validator addresses on the provider chain. Needed for the consumer initiated slashing sub-protocol.
```golang
ValidatorsByConsumerAddrBytePrefix | len(chainID) | chainID | consumerConsAddress -> providerConsAddress
```
- `ConsumerAddrsToPrune` - Stores the mapping from VSC ids to consumer validators addresses. Needed for pruning `ValidatorByConsumerAddr`. 
```golang
ConsumerAddrsToPruneBytePrefix | len(chainID) | chainID | vscID -> []consumerConsAddresses
```

### Protocol overview 

On receiving a `MsgAssignConsumerKey(chainID, providerAddr, consumerKey)` message:
```golang
// get validator from staking module  
validator, found := stakingKeeper.GetValidator(providerAddr)
if !found {
    return ErrNoValidatorFound
}
providerConsAddr := validator.GetConsAddr()

// make sure consumer key is not in use
consumerAddr := utils.TMCryptoPublicKeyToConsAddr(consumerKey)
if _, found := GetValidatorByConsumerAddr(ChainID, consumerAddr); found {
    return ErrInvalidConsumerConsensusPubKey
}

// check whether the consumer chain is already registered
// i.e., a client to the consumer was already created
if _, consumerRegistered := GetConsumerClientId(chainID); consumerRegistered {
    // get the previous key assigned for this validator on this consumer chain
    oldConsumerKey, found := GetValidatorConsumerPubKey(chainID, providerConsAddr)
    if found {
        // mark this old consumer key as prunable once the VSCMaturedPacket
        // for the current VSC ID is received
        oldConsumerAddr := utils.TMCryptoPublicKeyToConsAddr(oldConsumerKey)
        vscID := GetValidatorSetUpdateId()
        AppendConsumerAddrsToPrune(chainID, vscID, oldConsumerAddr)
    }
} else {
    // if the consumer chain is not registered, then remove the previous reverse mapping
    if oldConsumerKey, found := GetValidatorConsumerPubKey(chainID, providerConsAddr); found {
        oldConsumerAddr := utils.TMCryptoPublicKeyToConsAddr(oldConsumerKey)
        DeleteValidatorByConsumerAddr(chainID, oldConsumerAddr)
    }
}


// set the mapping from this validator's provider address to the new consumer key
SetValidatorConsumerPubKey(chainID, providerConsAddr, consumerKey)

// set the reverse mapping: from this validator's new consensus address 
// on the consumer to its consensus address on the provider
SetValidatorByConsumerAddr(chainID, consumerAddr, providerConsAddr)
```

When a new consumer chain is registered, i.e., a client to the consumer chain is created, the provider constructs the consumer CCV module part of the genesis state (see `MakeConsumerGenesis`). 
```golang
func (k Keeper) MakeConsumerGenesis(chainID string) (gen consumertypes.GenesisState, nextValidatorsHash []byte, err error) {
    // ...
    // get initial valset from the staking module
    var updates []abci.ValidatorUpdate{}
    stakingKeeper.IterateLastValidatorPowers(func(providerAddr sdk.ValAddress, power int64) (stop bool) {
        validator := stakingKeeper.GetValidator(providerAddr)
        providerKey := validator.TmConsPublicKey()
		updates = append(updates, abci.ValidatorUpdate{PubKey: providerKey, Power: power})
		return false
	})

    // applies the key assignment to the initial validator
	for i, update := range updates {
		providerAddr := utils.TMCryptoPublicKeyToConsAddr(update.PubKey)
		if consumerKey, found := GetValidatorConsumerPubKey(chainID, providerAddr); found {
			updates[i].PubKey = consumerKey
		}
	}
    gen.InitialValSet = updates

    // get a hash of the consumer validator set from the update
	updatesAsValSet := tendermint.PB2TM.ValidatorUpdates(updates)
	hash := tendermint.NewValidatorSet(updatesAsValSet).Hash()

	return gen, hash, nil
}
```

Note that key assignment works hand-in-hand with [epochs](https://github.com/cosmos/interchain-security/blob/main/docs/docs/adrs/adr-014-epochs.md).
For each consumer chain, we store the consumer validator set that is currently (i.e., in this epoch) validating the consumer chain. 
Specifically, for each validator in the set we store among others, the public key that it is using on the consumer chain during the current (i.e., ongoing) epoch.
At the end of every epoch, if there were validator set changes on the provider, then for every consumer chain, we construct a `VSCPacket` 
with all the validator updates and add it to the list of `PendingVSCPacket`s. We compute the validator updates needed by a consumer chain by
comparing the stored list of consumer validators with the current bonded validators on the provider, with something similar to this:
```golang
// get the valset that has been validating the consumer chain during this epoch 
currentValidators := GetConsumerValSet(consumerChain)
// generate the validator updates needed to be sent through a `VSCPacket` by comparing the current validators 
// in the epoch with the latest bonded validators
valUpdates := DiffValidators(currentValidators, stakingmodule.GetBondedValidators())
// update the current validators set for the upcoming epoch to be the latest bonded validators instead
SetConsumerValSet(stakingmodule.GetBondedValidators())
```
where `DiffValidators` internally checks if the consumer public key for a validator has changed since the last
epoch and if so generates a validator update. This way, a validator can change its consumer public key for a consumer
chain an arbitrary amount of times and only the last set consumer public key would be taken into account.

On receiving a `SlashPacket` from a consumer chain with id `chainID` for a infraction of a validator `data.Validator`:
```golang
func HandleSlashPacket(chainID string, data ccv.SlashPacketData) (success bool, err error) {
    // ...
    // the slash packet validator address may be known only on the consumer chain;
	// in this case, it must be mapped back to the consensus address on the provider chain
    consumerAddr := sdk.ConsAddress(data.Validator.Address)
    providerAddr, found := GetValidatorByConsumerAddr(chainID, consumerAddr)
    if !found {
        // the validator has the same key on the consumer as on the provider
        providerAddr = consumerAddr
    }
    // ...
}
```

On receiving a `VSCMatured`:
```golang
func OnRecvVSCMaturedPacket(packet channeltypes.Packet, data ccv.VSCMaturedPacketData) exported.Acknowledgement {
    // ...
    // prune previous consumer validator address that are no longer needed
    consumerAddrs := GetConsumerAddrsToPrune(chainID, data.ValsetUpdateId)
	for _, addr := range consumerAddrs {
		DeleteValidatorByConsumerAddr(chainID, addr)
	}
	DeleteConsumerAddrsToPrune(chainID, data.ValsetUpdateId)
    // ...
}
```

On stopping a consumer chain:
```golang
func (k Keeper) StopConsumerChain(ctx sdk.Context, chainID string, closeChan bool) (err error) {
    // ...
    // deletes all the state needed for key assignments on this consumer chain
    // ...
}
```

## Consequences

### Positive

- Validators can use different consensus keys on the consumer chains.

### Negative

- None

### Neutral

- The consensus state necessary to create a client to the consumer chain must use the hash returned by the `MakeConsumerGenesis` method as the `nextValsHash`.
- The consumer chain can no longer check the initial validator set against the consensus state on `InitGenesis`.

## References

* [Key assignment issue](https://github.com/cosmos/interchain-security/issues/26)
