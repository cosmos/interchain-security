package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	utils "github.com/cosmos/interchain-security/x/ccv/utils"
	abci "github.com/tendermint/tendermint/abci/types"
	tmprotocrypto "github.com/tendermint/tendermint/proto/tendermint/crypto"
)

type VSCID = uint64
type ProviderKey = tmprotocrypto.PublicKey
type ConsumerKey = tmprotocrypto.PublicKey
type ProviderAddr = sdk.ConsAddress
type ConsumerAddr = sdk.ConsAddress

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

func (k Keeper) IterateConsumerKeys(ctx sdk.Context, chainID string, cb func(providerAddr ProviderAddr, consumerKey ConsumerKey) bool) {
	store := ctx.KVStore(k.storeKey)
	prefix := types.ChainIdWithLenKey(types.ConsumerKeysPrefix, chainID)
	iter := sdk.KVStorePrefixIterator(store, prefix)
	defer iter.Close()
	for ; iter.Valid(); iter.Next() {
		providerAddr := ProviderAddr(iter.Key()[len(prefix):])
		var consumerKey ConsumerKey
		err := consumerKey.Unmarshal(iter.Value())
		if err != nil {
			panic(err)
		}
		if !cb(providerAddr, consumerKey) {
			break
		}
	}
}

func (k Keeper) DeleteConsumerKey(ctx sdk.Context, chainID string, providerAddr ProviderAddr) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerKeysKey(chainID, providerAddr))
}

func (k Keeper) ExportConsumerKeys(ctx sdk.Context) (consumerKeys []*types.ConsumerKeyRecord) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte{types.ConsumerKeysPrefix})
	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		chainID, providerAddr, err := types.ParseConsumerKeysKey(iterator.Key())
		if err != nil {
			panic(err)
		}
		var consumerKey ConsumerKey
		err = consumerKey.Unmarshal(iterator.Value())
		if err != nil {
			panic(err)
		}
		consumerKeys = append(consumerKeys, &types.ConsumerKeyRecord{
			ChainId:      chainID,
			ProviderAddr: providerAddr,
			ConsumerKey:  &consumerKey,
		})
	}
	return consumerKeys
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

func (k Keeper) IterateValidatorsByConsumerAddr(ctx sdk.Context, chainID string, cb func(consumerAddr ConsumerAddr, providerAddr ProviderAddr) (stop bool)) {
	store := ctx.KVStore(k.storeKey)
	prefix := types.ChainIdWithLenKey(types.ValidatorsByConsumerAddrPrefix, chainID)
	iter := sdk.KVStorePrefixIterator(store, prefix)
	defer iter.Close()
	for ; iter.Valid(); iter.Next() {
		consumerAddr := ConsumerAddr(iter.Key()[len(prefix):])
		var providerAddr ProviderAddr
		err := providerAddr.Unmarshal(iter.Value())
		if err != nil {
			panic(err)
		}
		if cb(consumerAddr, providerAddr) {
			break
		}
	}
}

func (k Keeper) DeleteValidatorByConsumerAddr(ctx sdk.Context, chainID string, consumerAddr ConsumerAddr) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ValidatorsByConsumerAddrKey(chainID, consumerAddr))
}

func (k Keeper) ExportValidatorsByConsumerAddr(ctx sdk.Context) (validatorsByConsumerAddr []*types.ValidatorByConsumerAddrRecord) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte{types.ValidatorsByConsumerAddrPrefix})
	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		chainID, consumerAddr, err := types.ParseValidatorsByConsumerAddrKey(iterator.Key())
		if err != nil {
			panic(err)
		}
		var providerAddr ProviderAddr
		err = providerAddr.Unmarshal(iterator.Value())
		if err != nil {
			panic(err)
		}
		validatorsByConsumerAddr = append(validatorsByConsumerAddr, &types.ValidatorByConsumerAddrRecord{
			ChainId:      chainID,
			ConsumerAddr: consumerAddr,
			ProviderAddr: providerAddr,
		})
	}
	return validatorsByConsumerAddr
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
	var consumerAddrsToPrune types.AddrList
	if bz != nil {
		err := consumerAddrsToPrune.Unmarshal(bz)
		if err != nil {
			panic(err)
		}
	}
	consumerAddrsToPrune.Addrs = append(consumerAddrsToPrune.Addrs, consumerAddr)
	bz, err := consumerAddrsToPrune.Marshal()
	if err != nil {
		panic(err)
	}
	store.Set(types.ConsumerAddrsToPruneKey(chainID, vscID), bz)
}

func (k Keeper) GetConsumerAddrsToPrune(ctx sdk.Context, chainID string, vscID VSCID) [][]byte {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerAddrsToPruneKey(chainID, vscID))
	if bz == nil {
		return nil
	}
	var consumerAddrsToPrune types.AddrList
	err := consumerAddrsToPrune.Unmarshal(bz)
	if err != nil {
		panic(err)
	}

	return consumerAddrsToPrune.Addrs
}

func (k Keeper) IterateConsumerAddrsToPrune(ctx sdk.Context, chainID string, cb func(vscID VSCID, consumerAddrsToPrune types.AddrList) (stop bool)) {
	store := ctx.KVStore(k.storeKey)
	iteratorPrefix := types.ChainIdWithLenKey(types.ConsumerAddrsToPrunePrefix, chainID)
	iterator := sdk.KVStorePrefixIterator(store, iteratorPrefix)
	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		var consumerAddrsToPrune types.AddrList
		err := consumerAddrsToPrune.Unmarshal(iterator.Value())
		if err != nil {
			panic(err)
		}
		vscID := sdk.BigEndianToUint64(iterator.Key()[len(iteratorPrefix):])
		if cb(vscID, consumerAddrsToPrune) {
			break
		}
	}
}

func (k Keeper) DeleteConsumerAddrsToPrune(ctx sdk.Context, chainID string, vscID VSCID) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerAddrsToPruneKey(chainID, vscID))
}

func (k Keeper) ExportConsumerAddrsToPrune(ctx sdk.Context) (consumerAddrsToPrune []*types.ConsumerAddrsToPruneRecord) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte{types.ConsumerAddrsToPrunePrefix})
	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		chainID, vscID, err := types.ParseConsumerAddrsToPruneKey(iterator.Key())
		if err != nil {
			panic(err)
		}
		var addrList types.AddrList
		err = addrList.Unmarshal(iterator.Value())
		if err != nil {
			panic(err)
		}
		consumerAddrsToPrune = append(consumerAddrsToPrune, &types.ConsumerAddrsToPruneRecord{
			ChainId: chainID,
			VscId:   vscID,
			Addrs:   addrList.Addrs,
		})
	}
	return consumerAddrsToPrune
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

func (k Keeper) ApplyKeyAssignmentToValUpdates(ctx sdk.Context, chainID string, valUpdates []abci.ValidatorUpdate) (newUpdates []abci.ValidatorUpdate, err error) {
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
func (k Keeper) PruneKeyAssignments(ctx sdk.Context, chainID string, vscID uint64) {
	cAddrs := k.GetConsumerAddrsToPrune(ctx, chainID, vscID)

	for _, cAddr := range cAddrs {
		k.DeleteValidatorByConsumerAddr(ctx, chainID, cAddr)
	}
}

// DeleteKeyAssignment deletes all records related to key assignment for a given consumer chain
// by deleting all ConsumerKeys, ValidatorsByConsumerAddr, PendingKeyAssignments and ConsumerAddrsToPrune
// records under that chainID.
func (k Keeper) DeleteKeyAssignmentByChainId(ctx sdk.Context, chainID string) {
	k.IterateConsumerKeys(ctx, chainID, func(pAddr ProviderAddr, cKey ConsumerKey) (stop bool) {
		k.DeleteConsumerKey(ctx, chainID, pAddr)
		return false
	})

	k.IterateValidatorsByConsumerAddr(ctx, chainID, func(cAddr ConsumerAddr, pAddr ProviderAddr) (stop bool) {
		k.DeleteValidatorByConsumerAddr(ctx, chainID, cAddr)
		return false
	})

	k.IteratePendingKeyAssignments(ctx, chainID, func(pAddr ProviderAddr, pendingKeyAssignment types.PendingKeyAssignment) (stop bool) {
		k.DeletePendingKeyAssignment(ctx, chainID, pAddr)
		return false
	})

	k.IterateConsumerAddrsToPrune(ctx, chainID, func(vscID uint64, _ types.AddrList) (stop bool) {
		k.DeleteConsumerAddrsToPrune(ctx, chainID, vscID)
		return false
	})
}

func (k Keeper) DeleteKeyAssignmentByValidator(ctx sdk.Context, chainID string, pAddr ProviderAddr) {
	cKey, found := k.GetConsumerKey(ctx, chainID, pAddr)

	if found {
		currentCAddr := utils.TMCryptoPublicKeyToConsAddr(cKey)
		k.DeleteConsumerKey(ctx, chainID, pAddr)
		k.DeletePendingKeyAssignment(ctx, chainID, pAddr)

		// This deletes the current key assignment in ValidatorsByConsumerAddr
		// there may be other key assignments in ValidatorsByConsumerAddr waiting to be pruned
		// but we don't need to delete them here because they will be pruned eventually.
		k.DeleteValidatorByConsumerAddr(ctx, chainID, currentCAddr)
	}
}
