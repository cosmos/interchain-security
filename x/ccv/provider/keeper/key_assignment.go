package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	utils "github.com/cosmos/interchain-security/x/ccv/utils"

	abci "github.com/tendermint/tendermint/abci/types"
	tmprotocrypto "github.com/tendermint/tendermint/proto/tendermint/crypto"
)

// GetValidatorConsumerPubKey returns a validator's public key assigned for a consumer chain
func (k Keeper) GetValidatorConsumerPubKey(
	ctx sdk.Context,
	chainID string,
	providerAddr sdk.ConsAddress,
) (consumerKey tmprotocrypto.PublicKey, found bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerValidatorsKey(chainID, providerAddr))
	if bz == nil {
		return consumerKey, false
	}
	err := consumerKey.Unmarshal(bz)
	if err != nil {
		panic(err)
	}
	return consumerKey, true
}

// SetValidatorConsumerPubKey sets a validator's public key assigned for a consumer chain
func (k Keeper) SetValidatorConsumerPubKey(
	ctx sdk.Context,
	chainID string,
	providerAddr sdk.ConsAddress,
	consumerKey tmprotocrypto.PublicKey,
) {
	store := ctx.KVStore(k.storeKey)
	bz, err := consumerKey.Marshal()
	if err != nil {
		panic(err)
	}
	store.Set(types.ConsumerValidatorsKey(chainID, providerAddr), bz)
}

// GetAllValidatorConsumerPubKeys gets all the validators public keys assigned for a consumer chain
// If chainID is nil, it returns all the validators public keys assigned for all consumer chains
//
// Note that the validators public keys assigned for a consumer chain are stored under keys
// with the following format: UnbondingOpIndexBytePrefix | len(chainID) | chainID | providerAddress
// Thus, the returned array is
//   - in ascending order of providerAddresses, if chainID is not nil;
//   - in undetermined order, if chainID is nil.
func (k Keeper) GetAllValidatorConsumerPubKeys(ctx sdk.Context, chainID *string) (validatorConsumerPubKeys []types.ValidatorConsumerPubKey) {
	store := ctx.KVStore(k.storeKey)
	var prefix []byte
	if chainID == nil {
		// iterate over the validators public keys assigned for all consumer chains
		prefix = []byte{types.ConsumerValidatorsBytePrefix}
	} else {
		// iterate over the validators public keys assigned for chainID
		prefix = types.ChainIdWithLenKey(types.ConsumerValidatorsBytePrefix, *chainID)
	}
	iterator := sdk.KVStorePrefixIterator(store, prefix)
	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		chainID, providerAddr, err := types.ParseChainIdAndConsAddrKey(types.ConsumerValidatorsBytePrefix, iterator.Key())
		if err != nil {
			panic(err)
		}
		var consumerKey tmprotocrypto.PublicKey
		err = consumerKey.Unmarshal(iterator.Value())
		if err != nil {
			panic(err)
		}

		validatorConsumerPubKeys = append(validatorConsumerPubKeys, types.ValidatorConsumerPubKey{
			ChainId:      chainID,
			ProviderAddr: providerAddr,
			ConsumerKey:  &consumerKey,
		})
	}

	return validatorConsumerPubKeys
}

// DeleteValidatorConsumerPubKey deletes a validator's public key assigned for a consumer chain
func (k Keeper) DeleteValidatorConsumerPubKey(ctx sdk.Context, chainID string, providerAddr sdk.ConsAddress) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerValidatorsKey(chainID, providerAddr))
}

// GetValidatorByConsumerAddr returns a validator's consensus address on the provider
// given the validator's consensus address on a consumer
func (k Keeper) GetValidatorByConsumerAddr(
	ctx sdk.Context,
	chainID string,
	consumerAddr sdk.ConsAddress,
) (providerAddr sdk.ConsAddress, found bool) {
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

// SetValidatorByConsumerAddr sets the mapping from a validator's consensus address on a consumer
// to the validator's consensus address on the provider
func (k Keeper) SetValidatorByConsumerAddr(
	ctx sdk.Context,
	chainID string,
	consumerAddr sdk.ConsAddress,
	providerAddr sdk.ConsAddress,
) {
	store := ctx.KVStore(k.storeKey)
	bz, err := providerAddr.Marshal()
	if err != nil {
		panic(err)
	}
	store.Set(types.ValidatorsByConsumerAddrKey(chainID, consumerAddr), bz)
}

// GetValidatorsByConsumerAddrs gets all the mappings from consensus addresses
// on a given consumer chain to consensus addresses on the provider chain.
// If chainID is nil, it returns all the mappings from consensus addresses on all consumer chains.
//
// Note that the mappings for a consumer chain are stored under keys with the following format:
// ValidatorsByConsumerAddrBytePrefix | len(chainID) | chainID | consumerAddress
// Thus, the returned array is
//   - in ascending order of consumerAddresses, if chainID is not nil;
//   - in undetermined order, if chainID is nil.
func (k Keeper) GetAllValidatorsByConsumerAddr(ctx sdk.Context, chainID *string) (validatorConsumerAddrs []types.ValidatorByConsumerAddr) {
	store := ctx.KVStore(k.storeKey)
	var prefix []byte
	if chainID == nil {
		// iterate over the mappings from consensus addresses on all consumer chains
		prefix = []byte{types.ValidatorsByConsumerAddrBytePrefix}
	} else {
		// iterate over the mappings from consensus addresses on chainID
		prefix = types.ChainIdWithLenKey(types.ValidatorsByConsumerAddrBytePrefix, *chainID)
	}
	iterator := sdk.KVStorePrefixIterator(store, prefix)
	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		chainID, consumerAddr, err := types.ParseChainIdAndConsAddrKey(types.ValidatorsByConsumerAddrBytePrefix, iterator.Key())
		if err != nil {
			panic(err)
		}
		var providerAddr sdk.ConsAddress
		err = providerAddr.Unmarshal(iterator.Value())
		if err != nil {
			panic(err)
		}

		validatorConsumerAddrs = append(validatorConsumerAddrs, types.ValidatorByConsumerAddr{
			ConsumerAddr: consumerAddr,
			ProviderAddr: providerAddr,
			ChainId:      chainID,
		})
	}

	return validatorConsumerAddrs
}

// DeleteValidatorByConsumerAddr deletes the mapping from a validator's consensus address on a consumer
// to the validator's consensus address on the provider
func (k Keeper) DeleteValidatorByConsumerAddr(ctx sdk.Context, chainID string, consumerAddr sdk.ConsAddress) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ValidatorsByConsumerAddrKey(chainID, consumerAddr))
}

// GetKeyAssignmentReplacement returns the previous assigned consumer key and the current power
// for a provider validator for which a key assignment was received in this block. Both are
// needed to update the validator's power on the consumer chain at the end of the current block.
func (k Keeper) GetKeyAssignmentReplacement(
	ctx sdk.Context,
	chainID string,
	providerAddr sdk.ConsAddress,
) (prevCKey tmprotocrypto.PublicKey, power int64, found bool) {
	var pubKeyAndPower abci.ValidatorUpdate
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.KeyAssignmentReplacementsKey(chainID, providerAddr))
	if bz == nil {
		return pubKeyAndPower.PubKey, pubKeyAndPower.Power, false
	}

	err := pubKeyAndPower.Unmarshal(bz)
	if err != nil {
		panic(err)
	}
	return pubKeyAndPower.PubKey, pubKeyAndPower.Power, true
}

// SetKeyAssignmentReplacement sets the previous assigned consumer key and the current power
// for a provider validator for which a key assignment was received in this block. Both are
// needed to update the validator's power on the consumer chain at the end of the current block.
func (k Keeper) SetKeyAssignmentReplacement(
	ctx sdk.Context,
	chainID string,
	providerAddr sdk.ConsAddress,
	prevCKey tmprotocrypto.PublicKey,
	power int64,
) {
	store := ctx.KVStore(k.storeKey)
	pubKeyAndPower := abci.ValidatorUpdate{PubKey: prevCKey, Power: power}
	bz, err := pubKeyAndPower.Marshal()
	if err != nil {
		panic(err)
	}
	store.Set(types.KeyAssignmentReplacementsKey(chainID, providerAddr), bz)
}

// GetAllKeyAssignmentReplacements gets all pairs of previous assigned consumer keys
// and current powers for all provider validator for which key assignments were received in this block.
//
// Note that the pairs are stored under keys with the following format:
// KeyAssignmentReplacementsBytePrefix | len(chainID) | chainID | providerAddress
// Thus, the iteration is in ascending order of providerAddresses.
func (k Keeper) GetAllKeyAssignmentReplacements(ctx sdk.Context, chainID string) (replacements []types.KeyAssignmentReplacement) {
	store := ctx.KVStore(k.storeKey)
	iteratorPrefix := types.ChainIdWithLenKey(types.KeyAssignmentReplacementsBytePrefix, chainID)
	iterator := sdk.KVStorePrefixIterator(store, iteratorPrefix)
	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		_, providerAddr, err := types.ParseChainIdAndConsAddrKey(types.KeyAssignmentReplacementsBytePrefix, iterator.Key())
		if err != nil {
			panic(err)
		}
		var pubKeyAndPower abci.ValidatorUpdate
		err = pubKeyAndPower.Unmarshal(iterator.Value())
		if err != nil {
			panic(err)
		}

		replacements = append(replacements, types.KeyAssignmentReplacement{
			ProviderAddr: providerAddr,
			PrevCKey:     &pubKeyAndPower.PubKey,
			Power:        pubKeyAndPower.Power,
		})
	}

	return replacements
}

// DeleteKeyAssignmentReplacement deletes the previous assigned consumer key and the current power
// for a provider validator for which a key assignment was received in this block. Both are
// needed to update the validator's power on the consumer chain at the end of the current block.
func (k Keeper) DeleteKeyAssignmentReplacement(ctx sdk.Context, chainID string, providerAddr sdk.ConsAddress) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.KeyAssignmentReplacementsKey(chainID, providerAddr))
}

// AppendConsumerAddrsToPrune appends a consumer validator address to the list of consumer addresses
// that can be pruned once the VSCMaturedPacket with vscID is received.
//
// The following invariant needs to hold:
// For each consumer address cAddr in ValidatorByConsumerAddr,
//   - either there exists a provider address pAddr in ValidatorConsumerPubKey,
//     s.t. hash(ValidatorConsumerPubKey(pAddr)) = cAddr
//   - or there exists a vscID in ConsumerAddrsToPrune s.t. cAddr in ConsumerAddrsToPrune(vscID)
func (k Keeper) AppendConsumerAddrsToPrune(ctx sdk.Context, chainID string, vscID uint64, consumerAddr sdk.ConsAddress) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerAddrsToPruneKey(chainID, vscID))
	var consumerAddrsToPrune types.AddressList
	if bz != nil {
		err := consumerAddrsToPrune.Unmarshal(bz)
		if err != nil {
			panic(err)
		}
	}
	consumerAddrsToPrune.Addresses = append(consumerAddrsToPrune.Addresses, consumerAddr)
	bz, err := consumerAddrsToPrune.Marshal()
	if err != nil {
		panic(err)
	}
	store.Set(types.ConsumerAddrsToPruneKey(chainID, vscID), bz)
}

// GetConsumerAddrsToPrune returns the list of consumer addresses
// that can be pruned once the VSCMaturedPacket with vscID is received
func (k Keeper) GetConsumerAddrsToPrune(
	ctx sdk.Context,
	chainID string,
	vscID uint64,
) (consumerAddrsToPrune types.AddressList) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerAddrsToPruneKey(chainID, vscID))
	if bz == nil {
		return
	}
	err := consumerAddrsToPrune.Unmarshal(bz)
	if err != nil {
		panic(err)
	}
	return
}

// GetAllConsumerAddrsToPrune gets all consumer addresses that can be pruned for a given chainID.
//
// Note that the list of all consumer addresses is stored under keys with the following format:
// ConsumerAddrsToPruneBytePrefix | len(chainID) | chainID | vscID
// Thus, the returned array is in ascending order of vscIDs.
func (k Keeper) GetAllConsumerAddrsToPrune(ctx sdk.Context, chainID string) (consumerAddrsToPrune []types.ConsumerAddrsToPrune) {
	store := ctx.KVStore(k.storeKey)
	iteratorPrefix := types.ChainIdWithLenKey(types.ConsumerAddrsToPruneBytePrefix, chainID)
	iterator := sdk.KVStorePrefixIterator(store, iteratorPrefix)
	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		_, vscID, err := types.ParseChainIdAndUintIdKey(types.ConsumerAddrsToPruneBytePrefix, iterator.Key())
		if err != nil {
			panic(err)
		}
		var addrs types.AddressList
		err = addrs.Unmarshal(iterator.Value())
		if err != nil {
			panic(err)
		}

		consumerAddrsToPrune = append(consumerAddrsToPrune, types.ConsumerAddrsToPrune{
			VscId:         vscID,
			ConsumerAddrs: &addrs,
			ChainId:       chainID,
		})
	}

	return consumerAddrsToPrune
}

// DeleteConsumerAddrsToPrune deletes the list of consumer addresses mapped to a given VSC ID
func (k Keeper) DeleteConsumerAddrsToPrune(ctx sdk.Context, chainID string, vscID uint64) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerAddrsToPruneKey(chainID, vscID))
}

// AssignConsumerKey assigns the consumerKey to the validator with providerAddr
// on the consumer chain with ID chainID
func (k Keeper) AssignConsumerKey(
	ctx sdk.Context,
	chainID string,
	validator stakingtypes.Validator,
	consumerKey tmprotocrypto.PublicKey,
) error {

	consumerAddr := utils.TMCryptoPublicKeyToConsAddr(consumerKey)

	providerAddr, err := validator.GetConsAddr()

	if err != nil {
		return err
	}

	if existingVal, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, consumerAddr); found {
		// If there is a validator with using the consumer key to validate on the provider
		// we prevent assigning the consumer key, unless the validator is assigning validator.
		// This ensures that a validator joining the active set who has not explicitly assigned
		// a consumer key, will be able to use their provider key as consumer key (as per default).
		if existingVal.OperatorAddress != validator.OperatorAddress {
			return sdkerrors.Wrapf(
				types.ErrConsumerKeyInUse, "a different validator already uses the consumer key",
			)
		}
	}

	if _, found := k.GetValidatorByConsumerAddr(ctx, chainID, consumerAddr); found {
		// consumer key is already in use
		// prevent multiple validators from assigning the same key
		return sdkerrors.Wrapf(
			types.ErrConsumerKeyInUse, "a validator has assigned the consumer key already",
		)
	}

	// check whether the consumer chain is already registered,
	// i.e., a client to the consumer was already created
	if _, consumerRegistered := k.GetConsumerClientId(ctx, chainID); consumerRegistered {
		// get the previous key assigned for this validator on this consumer chain
		oldConsumerKey, found := k.GetValidatorConsumerPubKey(ctx, chainID, providerAddr)
		if found {
			// mark this old consumer key as prunable once the VSCMaturedPacket
			// for the current VSC ID is received;
			// note: this state is removed on receiving the VSCMaturedPacket
			k.AppendConsumerAddrsToPrune(
				ctx,
				chainID,
				k.GetValidatorSetUpdateId(ctx),
				utils.TMCryptoPublicKeyToConsAddr(oldConsumerKey),
			)
		} else {
			// the validator had no key assigned on this consumer chain
			providerKey, err := validator.TmConsPublicKey()
			if err != nil {
				return err
			}
			oldConsumerKey = providerKey
		}

		// check whether the validator is valid, i.e., its power is positive
		power := k.stakingKeeper.GetLastValidatorPower(ctx, validator.GetOperator())
		if 0 < power {
			// to enable multiple calls of AssignConsumerKey in the same block by the same validator

			// the key assignment replacement should not be overwritten
			if _, _, found := k.GetKeyAssignmentReplacement(ctx, chainID, providerAddr); !found {
				// store old key and current power for modifying the valset update in EndBlock;
				// note: this state is deleted at the end of the block
				k.SetKeyAssignmentReplacement(
					ctx,
					chainID,
					providerAddr,
					oldConsumerKey,
					power,
				)
			}
		}
	} else {
		// if the consumer chain is not registered, then remove the mapping
		// from the old consumer address to the provider address (if any)
		// get the previous key assigned for this validator on this consumer chain
		if oldConsumerKey, found := k.GetValidatorConsumerPubKey(ctx, chainID, providerAddr); found {
			k.DeleteValidatorByConsumerAddr(
				ctx,
				chainID,
				utils.TMCryptoPublicKeyToConsAddr(oldConsumerKey),
			)
		}
	}

	// set the mapping from this validator's provider address to the new consumer key;
	// overwrite if already exists
	// note: this state is deleted when the validator is removed from the staking module
	k.SetValidatorConsumerPubKey(ctx, chainID, providerAddr, consumerKey)

	// set the mapping from this validator's new consensus address on the consumer
	// to its consensus address on the provider;
	// note: this state must be deleted through the pruning mechanism
	k.SetValidatorByConsumerAddr(ctx, chainID, consumerAddr, providerAddr)

	return nil
}

// ApplyKeyAssignmentToValUpdates applies the key assignment to the validator updates
// received from the staking module
func (k Keeper) ApplyKeyAssignmentToValUpdates(
	ctx sdk.Context,
	chainID string,
	valUpdates []abci.ValidatorUpdate,
) (newUpdates []abci.ValidatorUpdate, err error) {
	for _, valUpdate := range valUpdates {
		providerAddr := utils.TMCryptoPublicKeyToConsAddr(valUpdate.PubKey)

		// If a key assignment replacement is found, we remove the valupdate with the old consumer key,
		// create two new valupdates,
		//  - setting the old consumer key's power to 0
		//  - and setting the new consumer key's power to the power in the update
		prevConsumerKey, _, found := k.GetKeyAssignmentReplacement(ctx, chainID, providerAddr)
		if found {
			newUpdates = append(newUpdates, abci.ValidatorUpdate{
				PubKey: prevConsumerKey,
				Power:  0,
			})

			newConsumerKey, found := k.GetValidatorConsumerPubKey(ctx, chainID, providerAddr)
			if !found {
				return newUpdates, sdkerrors.Wrapf(types.ErrConsumerKeyNotFound, "consumer key not found for %s", providerAddr)
			}
			newUpdates = append(newUpdates, abci.ValidatorUpdate{
				PubKey: newConsumerKey,
				Power:  valUpdate.Power,
			})
			k.DeleteKeyAssignmentReplacement(ctx, chainID, providerAddr)
		} else {
			// If a key assignment replacement is not found, we check if the validator's key is assigned.
			// If it is, we replace the update containing the provider key with an update containing
			// the consumer key.
			// Note that this will always be the brach taken when creating the genesis state
			// of a newly registered consumer chain.
			consumerKey, found := k.GetValidatorConsumerPubKey(ctx, chainID, providerAddr)
			if found {
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

	// For any key assignment replacements that did not have a corresponding validator update already,
	// set the old consumer key's power to 0 and the new consumer key's power to the
	// power in the pending key assignment.
	for _, replacement := range k.GetAllKeyAssignmentReplacements(ctx, chainID) {
		k.DeleteKeyAssignmentReplacement(ctx, chainID, replacement.ProviderAddr)
		newUpdates = append(newUpdates, abci.ValidatorUpdate{
			PubKey: *replacement.PrevCKey,
			Power:  0,
		})

		newConsumerKey, found := k.GetValidatorConsumerPubKey(ctx, chainID, replacement.ProviderAddr)
		if !found {
			return newUpdates, sdkerrors.Wrapf(types.ErrConsumerKeyNotFound, "consumer key not found for %s", replacement.ProviderAddr)
		}
		newUpdates = append(newUpdates, abci.ValidatorUpdate{
			PubKey: newConsumerKey,
			Power:  replacement.Power,
		})
	}

	return newUpdates, nil
}

// GetProviderAddrFromConsumerAddr returns the consensus address of a validator with
// consAddr set as the consensus address on a consumer chain
func (k Keeper) GetProviderAddrFromConsumerAddr(
	ctx sdk.Context,
	chainID string,
	consAddr sdk.ConsAddress,
) sdk.ConsAddress {
	// check if this address is known only to the consumer chain
	if providerConsAddr, found := k.GetValidatorByConsumerAddr(ctx, chainID, consAddr); found {
		return providerConsAddr
	}
	return consAddr
}

// PruneKeyAssignments prunes the consumer addresses no longer needed
// as they cannot be referenced in slash requests (by a correct consumer)
func (k Keeper) PruneKeyAssignments(ctx sdk.Context, chainID string, vscID uint64) {
	consumerAddrs := k.GetConsumerAddrsToPrune(ctx, chainID, vscID)
	for _, addr := range consumerAddrs.Addresses {
		k.DeleteValidatorByConsumerAddr(ctx, chainID, addr)
		k.Logger(ctx).Info("consumer address was pruned",
			"consumer chainID", chainID,
			"consumer consensus addr", sdk.ConsAddress(addr).String(),
		)
	}

	k.DeleteConsumerAddrsToPrune(ctx, chainID, vscID)
}

// DeleteKeyAssignments deletes all the state needed for key assignments on a consumer chain
func (k Keeper) DeleteKeyAssignments(ctx sdk.Context, chainID string) {
	// delete ValidatorConsumerPubKey
	for _, validatorConsumerAddr := range k.GetAllValidatorConsumerPubKeys(ctx, &chainID) {
		k.DeleteValidatorConsumerPubKey(ctx, chainID, validatorConsumerAddr.ProviderAddr)
	}

	// delete ValidatorsByConsumerAddr
	for _, validatorConsumerAddr := range k.GetAllValidatorsByConsumerAddr(ctx, &chainID) {
		k.DeleteValidatorByConsumerAddr(ctx, chainID, validatorConsumerAddr.ConsumerAddr)
	}

	// delete KeyAssignmentReplacements
	for _, keyAssignmentReplacement := range k.GetAllKeyAssignmentReplacements(ctx, chainID) {
		k.DeleteKeyAssignmentReplacement(ctx, chainID, keyAssignmentReplacement.ProviderAddr)
	}

	// delete ValidatorConsumerPubKey
	for _, consumerAddrsToPrune := range k.GetAllConsumerAddrsToPrune(ctx, chainID) {
		k.DeleteConsumerAddrsToPrune(ctx, chainID, consumerAddrsToPrune.VscId)
	}
}
