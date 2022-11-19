package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	utils "github.com/cosmos/interchain-security/x/ccv/utils"
	abci "github.com/tendermint/tendermint/abci/types"
)

// Indexes
//
// ConsumerKeys: chainID | providerAddr -> consumerKey
// ValidatorsByConsumerAddr: chainID | consumerAddr -> providerAddr
// PendingKeyAssignments: chainID | providerAddr -> {oldConsumerKey, oldPower}
// ConsumerAddrsToPrune: chainID | vscID -> List(consumerAddr)

func (k Keeper) GetConsumerKey(ctx sdk.Context, chainID string, providerAddr ProviderAddr) (consumerKey ConsumerKey, found bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerKeysKey(chainID, providerAddr))
	if bz == nil {
		return consumerKey, false
	}
	err := consumerKey.Unmarshal(bz)
	if err != nil {
		panic(err)
	}

	return consumerKey, true
}

func (k Keeper) SetConsumerKey(ctx sdk.Context, chainID string, providerAddr ProviderAddr, consumerKey ConsumerKey) {
	store := ctx.KVStore(k.storeKey)
	bz, err := consumerKey.Marshal()
	if err != nil {
		panic(err)
	}
	store.Set(types.ConsumerKeysKey(chainID, providerAddr), bz)
}

func (k Keeper) GetValidatorByConsumerAddr(ctx sdk.Context, chainID string, consumerAddr ConsumerAddr) (providerAddr ProviderAddr, found bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ValidatorsByConsumerAddrKey(chainID, consumerAddr))
	if bz == nil {
		return providerAddr, false
	}
	err := providerAddr.Unmarshal(bz)
	if err != nil {
		panic(err)
	}

	return providerAddr, true
}

func (k Keeper) SetValidatorByConsumerAddr(ctx sdk.Context, chainID string, consumerAddr ConsumerAddr, providerAddr ProviderAddr) {
	store := ctx.KVStore(k.storeKey)
	bz, err := providerAddr.Marshal()
	if err != nil {
		panic(err)
	}
	store.Set(types.ValidatorsByConsumerAddrKey(chainID, consumerAddr), bz)
}

func (k Keeper) DeleteValidatorByConsumerAddr(ctx sdk.Context, chainID string, consumerAddr ConsumerAddr) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ValidatorsByConsumerAddrKey(chainID, consumerAddr))
}

func (k Keeper) GetPendingKeyAssignment(ctx sdk.Context, chainID string, providerAddr ProviderAddr) (pendingKeyAssignment types.PendingKeyAssignment, found bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.PendingKeyAssignmentKey(chainID, providerAddr))
	if bz == nil {
		return pendingKeyAssignment, false
	}
	err := pendingKeyAssignment.Unmarshal(bz)
	if err != nil {
		panic(err)
	}

	return pendingKeyAssignment, true
}

func (k Keeper) SetPendingKeyAssignment(ctx sdk.Context, chainID string, providerAddr ProviderAddr, pendingKeyAssignment types.PendingKeyAssignment) {
	store := ctx.KVStore(k.storeKey)
	bz, err := pendingKeyAssignment.Marshal()
	if err != nil {
		panic(err)
	}
	store.Set(types.PendingKeyAssignmentKey(chainID, providerAddr), bz)
}

func (k Keeper) IteratePendingKeyAssignments(ctx sdk.Context, chainID string, cb func(providerAddr ProviderAddr, pendingKeyAssignment types.PendingKeyAssignment) (stop bool)) {
	store := ctx.KVStore(k.storeKey)
	iteratorPrefix := types.ChainIdWithLenKey(types.PendingKeyAssignmentPrefix, chainID)
	iterator := sdk.KVStorePrefixIterator(store, iteratorPrefix)
	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		var pendingKeyAssignment types.PendingKeyAssignment
		err := pendingKeyAssignment.Unmarshal(iterator.Value())
		if err != nil {
			panic(err)
		}
		var providerAddr ProviderAddr
		err = providerAddr.Unmarshal(iterator.Key()[len(iteratorPrefix):])
		if err != nil {
			panic(err)
		}
		if cb(providerAddr, pendingKeyAssignment) {
			break
		}
	}
}

func (k Keeper) DeletePendingKeyAssignment(ctx sdk.Context, chainID string, providerAddr ProviderAddr) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.PendingKeyAssignmentKey(chainID, providerAddr))
}

func (k Keeper) AppendConsumerAddrToPrune(ctx sdk.Context, chainID string, vscID VSCID, consumerAddr ConsumerAddr) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerAddrsToPruneKey(chainID, vscID))
	var consumerAddrsToPrune types.ConsumerAddrsToPrune
	if bz != nil {
		err := consumerAddrsToPrune.Unmarshal(bz)
		if err != nil {
			panic(err)
		}
	}
	consumerAddrsToPrune.ConsumerAddrs = append(consumerAddrsToPrune.ConsumerAddrs, consumerAddr)
	bz, err := consumerAddrsToPrune.Marshal()
	if err != nil {
		panic(err)
	}
	store.Set(types.ConsumerAddrsToPruneKey(chainID, vscID), bz)
}

// ConsumerAddrsToPrune is currently stored as a serialized list of consumer addresses. If necessary it will be possible to move to
// a more efficient storage format using a prefix iterator with this API.
func (k Keeper) IterateConsumerAddrsToPrune(ctx sdk.Context, chainID string, vscID VSCID, cb func(consumerAddr ConsumerAddr) (stop bool)) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerAddrsToPruneKey(chainID, vscID))
	if bz == nil {
		return
	}
	var consumerAddrsToPrune types.ConsumerAddrsToPrune
	err := consumerAddrsToPrune.Unmarshal(bz)
	if err != nil {
		panic(err)
	}
	for _, consumerAddr := range consumerAddrsToPrune.ConsumerAddrs {
		if cb(consumerAddr) {
			break
		}
	}
}

func (k Keeper) DeleteConsumerAddrsToPrune(ctx sdk.Context, chainID string, vscID VSCID) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerAddrsToPruneKey(chainID, vscID))
}

// on receiving KeyAssignMsg(pKey, chainID, cKey)
//
// pAddr := hash(pkey)
// val = staking.GetValidatorByConsAddr(pAddr)
// oldCKey, found := ConsumerKeys[chainID, pAddr]
// if !found {
//   oldCKey = pKey
// } else {
//   // the old consumer key can be pruned once the VSCPacket sent in EndBlock matures
//   ConsumerAddrsToPrune[chainID, k.GetValidatorSetUpdateId()].append(oldCKey)
// }
// oldPower = staking.GetLastValidatorPower(val.OperatorAddress)
// if 0 != oldPower {
//   // active validator; store old key and power for modifying the valupdate
//   PendingKeyAssignments[chainID, pAddr] = {oldCKey, oldPower}
// }
// ConsumerKeys[chainID, pAddr] = cKey // overwrite if already exists
// ValidatorsByConsumerAddr[chainID, hash(cKey)] = pKey // panic if already exists

func (k Keeper) AssignConsumerKey(ctx sdk.Context, chainID string, pKey ProviderKey, consumerKey ConsumerKey) error {
	pAddr := utils.TMCryptoPublicKeyToConsAddr(pKey)

	// Get the validator
	validator, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, pAddr)
	if !found {
		// panic("validator not found")
		return sdkerrors.Wrapf(types.ErrValidatorNotFound, "validator not found for %s", pAddr)
	}

	oldCKey, found := k.GetConsumerKey(ctx, chainID, pAddr)
	if !found {
		oldCKey = pKey
	} else {
		// the old consumer key can be pruned once the VSCPacket sent in EndBlock matures
		k.AppendConsumerAddrToPrune(ctx, chainID, k.GetValidatorSetUpdateId(ctx), utils.TMCryptoPublicKeyToConsAddr(oldCKey))
	}

	oldPower := k.stakingKeeper.GetLastValidatorPower(ctx, validator.GetOperator())

	if oldPower != 0 {
		// active validator; store old key and power for modifying the valupdate
		k.SetPendingKeyAssignment(ctx, chainID, pAddr, types.PendingKeyAssignment{
			ConsumerKey: &oldCKey,
			Power:       oldPower,
		})
	}

	k.SetConsumerKey(ctx, chainID, pAddr, consumerKey) // overwrite if already exists

	// error if already assigned
	_, found = k.GetValidatorByConsumerAddr(ctx, chainID, utils.TMCryptoPublicKeyToConsAddr(consumerKey))
	if found {
		return sdkerrors.Wrapf(types.ErrConsumerKeyAlreadyAssigned, "consumer key already assigned for %s", consumerKey)
	}

	k.SetValidatorByConsumerAddr(ctx, chainID, utils.TMCryptoPublicKeyToConsAddr(consumerKey), pAddr)

	return nil
}

// On EndBlock
//
// valUpdates := staking.GetValidatorUpdates()
// k.IterateConsumerChains {
//   for up := range valUpdates {
//     pAddr := hash(up.PubKey)
//     oldCKey, oldPower, found := PendingKeyAssignments[chainID, pAddr]
//     if found {
//       // remove up from valUpdates
//       // add both {oldCKey, 0} and {ConsumerKeys[chainID, pAddr], up.Power} to valUpdates
//       // delete PendingKeyAssignments[chainID, pAddr]
//     } else {
//       cKey, found := ConsumerKeys[chainID, pAddr]
//       if found {
//          // remove up from valUpdates
//          // add {ConsumerKeys[chainID, pAddr], up.Power} to valUpdates
//       }
//     }
//   }
//   for key, value := range PendingKeyAssignments[chainId] {
//     // add both {value.oldCKey, 0} and {ConsumerKeys[chainID, key.pAddr], value.oldPower} to valUpdates
//   }
// }

func (k Keeper) ApplyKeyAssignmentToValUpdates(ctx sdk.Context, valUpdates []abci.ValidatorUpdate, chainID string) (newUpdates []abci.ValidatorUpdate, err error) {
	var updatesToRemove []int
	var updatesToAdd []abci.ValidatorUpdate

	for i, valUpdate := range valUpdates {
		pAddr := utils.TMCryptoPublicKeyToConsAddr(valUpdate.PubKey)

		pendingKeyAssignment, found := k.GetPendingKeyAssignment(ctx, chainID, pAddr)
		oldCKey := pendingKeyAssignment.ConsumerKey

		// If a pending key assignment is found, we remove the valupdate with the old consumer key,
		// create a new valupdate setting the old consumer key's power to 0,
		// and create a new valupdate setting the new consumer key's power to the power in the update.
		if found {
			// remove up from valUpdates
			// add both {oldCKey, 0} and {ConsumerKeys[chainID, pAddr], up.Power} to valUpdates
			// delete PendingKeyAssignments[chainID, pAddr]
			updatesToRemove = append(updatesToRemove, i)
			updatesToAdd = append(updatesToAdd, abci.ValidatorUpdate{
				PubKey: *oldCKey,
				Power:  0,
			})

			newCKey, found := k.GetConsumerKey(ctx, chainID, pAddr)
			if !found {
				return newUpdates, sdkerrors.Wrapf(types.ErrConsumerKeyNotFound, "consumer key not found for %s", pAddr)
			}

			updatesToAdd = append(updatesToAdd, abci.ValidatorUpdate{
				PubKey: newCKey,
				Power:  valUpdate.Power,
			})

			k.DeletePendingKeyAssignment(ctx, chainID, pAddr)
		} else {
			// If a pending key assignment is not found, we check if the validator's key is assigned.
			// If it is, we replace the update containing the provider key with the update containing the consumer key.
			cKey, found := k.GetConsumerKey(ctx, chainID, pAddr)
			if found {
				// remove up from valUpdates
				// add {ConsumerKeys[chainID, pAddr], up.Power} to valUpdates
				updatesToRemove = append(updatesToRemove, i)
				updatesToAdd = append(updatesToAdd, abci.ValidatorUpdate{
					PubKey: cKey,
					Power:  valUpdate.Power,
				})
			}
		}
	}

	// Any pending key assignments did not have a corresponding validator update already have
	// their old consumer key's power set to 0 and their new consumer key's power set to the
	// power in the pending key assignment.
	k.IteratePendingKeyAssignments(ctx, chainID, func(
		pAddr sdk.ConsAddress,
		pendingKeyAssignment types.PendingKeyAssignment,
	) (stop bool) {
		// add both {value.oldCKey, 0} and {ConsumerKeys[chainID, key.pAddr], value.oldPower} to valUpdates
		updatesToAdd = append(updatesToAdd, abci.ValidatorUpdate{
			PubKey: *pendingKeyAssignment.ConsumerKey,
			Power:  0,
		})

		newCKey, found := k.GetConsumerKey(ctx, chainID, pAddr)
		if !found {
			err = sdkerrors.Wrapf(types.ErrConsumerKeyNotFound, "consumer key not found for %s", pAddr)
			return true
		}

		updatesToAdd = append(updatesToAdd, abci.ValidatorUpdate{
			PubKey: newCKey,
			Power:  pendingKeyAssignment.Power,
		})

		return false
	})

	if err != nil {
		return newUpdates, err
	}

	// Remove the updates that need to be removed
	for _, index := range updatesToRemove {
		valUpdates = append(valUpdates[:index], valUpdates[index+1:]...)
	}

	// Add the updates that need to be added
	valUpdates = append(valUpdates, updatesToAdd...)

	return valUpdates, nil
}

// on receiving a Slash packet use the ValidatorsByConsumerAddr index

// on receiving a VSCMaturedPacket from chainID
//
//	for cAddr := range ConsumerAddrsToPrune[chainID, data.vscID] {
//		delete ValidatorsByConsumerAddr[chainID, cAddr]
//	}
func (k Keeper) PruneValidatorsByConsumerAddr(ctx sdk.Context, chainID string, vscID uint64) {
	k.IterateConsumerAddrsToPrune(ctx, chainID, vscID, func(cAddr sdk.ConsAddress) (stop bool) {
		k.DeleteValidatorByConsumerAddr(ctx, chainID, cAddr)
		return false
	})
}
