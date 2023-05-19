---
sidebar_position: 3
title: Key Assignment
---

# ADR 001: Key Assignment

## Changelog
* 2022-12-01: Initial Draft

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
- `KeyAssignmentReplacements` - Stores the key assignments that need to be replaced in the current block. Needed to apply the key assignments received in a block to the validator updates sent to the consumer chains.
```golang
KeyAssignmentReplacementsBytePrefix | len(chainID) | chainID | providerConsAddress -> abci.ValidatorUpdate{PubKey: oldConsumerKey, Power: currentPower},
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
    } else {
        // the validator had no key assigned on this consumer chain
        oldConsumerKey := validator.TmConsPublicKey()
    }

    // check whether the validator is valid, i.e., its power is positive
    if currentPower := stakingKeeper.GetLastValidatorPower(providerAddr); currentPower > 0 {
        // to enable multiple calls of AssignConsumerKey in the same block by the same validator
        // the key assignment replacement should not be overwritten
        if _, found := GetKeyAssignmentReplacement(chainID, providerConsAddr); !found {
            // store old key and power for modifying the valset update in EndBlock
            oldKeyAssignment := abci.ValidatorUpdate{PubKey: oldConsumerKey, Power: currentPower}
            SetKeyAssignmentReplacement(chainID, providerConsAddr, oldKeyAssignment)
        }
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

On `EndBlock` while queueing `VSCPacket`s to send to registered consumer chains:
```golang
func QueueVSCPackets() {
	valUpdateID := GetValidatorSetUpdateId()
	// get the validator updates from the staking module
	valUpdates := stakingKeeper.GetValidatorUpdates()

	IterateConsumerChains(func(chainID, clientID string) (stop bool) {
		// apply the key assignment to the validator updates
		valUpdates := ApplyKeyAssignmentToValUpdates(chainID, valUpdates)
        // ..
    })
    // ...
}

func ApplyKeyAssignmentToValUpdates(
    chainID string, 
    valUpdates []abci.ValidatorUpdate,
) (newUpdates []abci.ValidatorUpdate) {
    for _, valUpdate := range valUpdates {
        providerAddr := utils.TMCryptoPublicKeyToConsAddr(valUpdate.PubKey)

        // if a key assignment replacement is found, then
        // remove the valupdate with the old consumer key
        // and create two new valupdates
        prevConsumerKey, _, found := GetKeyAssignmentReplacement(chainID, providerAddr)
        if found {
            // set the old consumer key's power to 0
            newUpdates = append(newUpdates, abci.ValidatorUpdate{
				PubKey: prevConsumerKey,
				Power:  0,
			})
		    // set the new consumer key's power to the power in the update
            newConsumerKey := GetValidatorConsumerPubKey(chainID, providerAddr)
			newUpdates = append(newUpdates, abci.ValidatorUpdate{
				PubKey: newConsumerKey,
				Power:  valUpdate.Power,
			})
            // delete key assignment replacement
			DeleteKeyAssignmentReplacement(chainID, providerAddr)
        } else {
            // there is no key assignment replacement;
            // check if the validator's key is assigned
            consumerKey, found := k.GetValidatorConsumerPubKey(ctx, chainID, providerAddr)
			if found {
                // replace the update containing the provider key 
                // with an update containing the consumer key
				newUpdates = append(newUpdates, abci.ValidatorUpdate{
					PubKey: consumerKey,
					Power:  valUpdate.Power,
				})
			} else {
				// keep the same update
				newUpdates = append(newUpdates, valUpdate)
			}
        }
    }

    // iterate over the remaining key assignment replacements
    IterateKeyAssignmentReplacements(chainID, func(
		pAddr sdk.ConsAddress,
		prevCKey tmprotocrypto.PublicKey,
		power int64,
	) (stop bool) {
       // set the old consumer key's power to 0
		newUpdates = append(newUpdates, abci.ValidatorUpdate{
			PubKey: prevCKey,
			Power:  0,
		})
        // set the new consumer key's power to the power in key assignment replacement
		newConsumerKey := GetValidatorConsumerPubKey(chainID, pAddr)
		newUpdates = append(newUpdates, abci.ValidatorUpdate{
			PubKey: newConsumerKey,
			Power:  power,
		})
		return false
	})

    // remove all the key assignment replacements
   
    return newUpdates
}
```

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
        providerAddr = consumer
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

* [Key assignment issue](https://github.com/octopus-network/interchain-security/issues/26)
