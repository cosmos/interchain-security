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

// IterateValidatorConsumerPubKeys iterates over the validators public keys assigned for a consumer chain
func (k Keeper) IterateValidatorConsumerPubKeys(
	ctx sdk.Context,
	chainID string,
	cb func(providerAddr sdk.ConsAddress, consumerKey tmprotocrypto.PublicKey) (stop bool),
) {
	store := ctx.KVStore(k.storeKey)
	prefix := types.ChainIdWithLenKey(types.ConsumerValidatorsBytePrefix, chainID)
	iter := sdk.KVStorePrefixIterator(store, prefix)
	defer iter.Close()
	for ; iter.Valid(); iter.Next() {
		_, providerAddr, err := types.ParseChainIdAndConsAddrKey(types.ConsumerValidatorsBytePrefix, iter.Key())
		if err != nil {
			panic(err)
		}
		var consumerKey tmprotocrypto.PublicKey
		err = consumerKey.Unmarshal(iter.Value())
		if err != nil {
			panic(err)
		}
		stop := cb(providerAddr, consumerKey)
		if stop {
			break
		}
	}
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

func (k Keeper) IterateValidatorsByConsumerAddr(
	ctx sdk.Context,
	chainID string,
	cb func(consumerAddr sdk.ConsAddress, providerAddr sdk.ConsAddress) (stop bool),
) {
	store := ctx.KVStore(k.storeKey)
	prefix := types.ChainIdWithLenKey(types.ValidatorsByConsumerAddrBytePrefix, chainID)
	iter := sdk.KVStorePrefixIterator(store, prefix)
	defer iter.Close()
	for ; iter.Valid(); iter.Next() {
		_, consumerAddr, err := types.ParseChainIdAndConsAddrKey(types.ValidatorsByConsumerAddrBytePrefix, iter.Key())
		if err != nil {
			panic(err)
		}
		var providerAddr sdk.ConsAddress
		err = providerAddr.Unmarshal(iter.Value())
		if err != nil {
			panic(err)
		}
		stop := cb(consumerAddr, providerAddr)
		if stop {
			break
		}
	}
}

// DeleteValidatorByConsumerAddr deletes the mapping from a validator's consensus address on a consumer
// to the validator's consensus address on the provider
func (k Keeper) DeleteValidatorByConsumerAddr(ctx sdk.Context, chainID string, consumerAddr sdk.ConsAddress) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ValidatorsByConsumerAddrKey(chainID, consumerAddr))
}

// GetPendingKeyAssignment returns the pending key assignment for a provider validator on a consumer chain
func (k Keeper) GetPendingKeyAssignment(
	ctx sdk.Context,
	chainID string,
	providerAddr sdk.ConsAddress,
) (pendingKeyAssignment abci.ValidatorUpdate, found bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.PendingKeyAssignmentsKey(chainID, providerAddr))
	if bz == nil {
		return pendingKeyAssignment, false
	}
	err := pendingKeyAssignment.Unmarshal(bz)
	if err != nil {
		panic(err)
	}
	return pendingKeyAssignment, true
}

// SetPendingKeyAssignment sets the pending key assignment for a provider validator on a consumer chain
func (k Keeper) SetPendingKeyAssignment(
	ctx sdk.Context,
	chainID string,
	providerAddr sdk.ConsAddress,
	pendingKeyAssignment abci.ValidatorUpdate,
) {
	store := ctx.KVStore(k.storeKey)
	bz, err := pendingKeyAssignment.Marshal()
	if err != nil {
		panic(err)
	}
	store.Set(types.PendingKeyAssignmentsKey(chainID, providerAddr), bz)
}

// IteratePendingKeyAssignments iterates through all pending key assignment for provider validators on a consumer chain
func (k Keeper) IteratePendingKeyAssignments(
	ctx sdk.Context,
	chainID string,
	cb func(providerAddr sdk.ConsAddress, pendingKeyAssignment abci.ValidatorUpdate) (stop bool),
) {
	store := ctx.KVStore(k.storeKey)
	iteratorPrefix := types.ChainIdWithLenKey(types.PendingKeyAssignmentsBytePrefix, chainID)
	iterator := sdk.KVStorePrefixIterator(store, iteratorPrefix)
	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		_, providerAddr, err := types.ParseChainIdAndConsAddrKey(types.PendingKeyAssignmentsBytePrefix, iterator.Key())
		if err != nil {
			panic(err)
		}
		var pendingKeyAssignment abci.ValidatorUpdate
		err = pendingKeyAssignment.Unmarshal(iterator.Value())
		if err != nil {
			panic(err)
		}
		stop := cb(providerAddr, pendingKeyAssignment)
		if stop {
			break
		}
	}
}

// DeletePendingKeyAssignment deletes the pending key assignment for a provider validator on a consumer chain
func (k Keeper) DeletePendingKeyAssignment(ctx sdk.Context, chainID string, providerAddr sdk.ConsAddress) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.PendingKeyAssignmentsKey(chainID, providerAddr))
}

// TODO mpoke: setters and getters for ConsumerValidatorsByVscID

// AppendConsumerValidatorByVscID appends a consumer validator address to the list of consumer addresses
// that can be pruned once the VSCMaturedPacket with vscID is received
func (k Keeper) AppendConsumerValidatorByVscID(ctx sdk.Context, chainID string, vscID uint64, consumerAddr sdk.ConsAddress) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerValidatorsByVscIDKey(chainID, vscID))
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
	store.Set(types.ConsumerValidatorsByVscIDKey(chainID, vscID), bz)
}

// GetConsumerValidatorByVscID returns the list of consumer addresses
// that can be pruned once the VSCMaturedPacket with vscID is received
func (k Keeper) GetConsumerValidatorByVscID(ctx sdk.Context, chainID string, vscID uint64) [][]byte {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerValidatorsByVscIDKey(chainID, vscID))
	if bz == nil {
		return nil
	}
	var consumerAddrsToPrune types.AddressList
	err := consumerAddrsToPrune.Unmarshal(bz)
	if err != nil {
		panic(err)
	}
	return consumerAddrsToPrune.Addresses
}

// DeleteConsumerValidatorByVscID deletes the list of consumer addresses mapped to a given VSC ID
func (k Keeper) DeleteConsumerValidatorByVscID(ctx sdk.Context, chainID string, vscID uint64) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerValidatorsByVscIDKey(chainID, vscID))
}

// AssignConsumerKey assigns the consumerKey to the validator with providerAddr
// on the consumer chain with ID chainID
func (k Keeper) AssignConsumerKey(
	ctx sdk.Context,
	chainID string,
	providerAddr sdk.ConsAddress,
	consumerKey tmprotocrypto.PublicKey,
) error {
	// validator must already be registered
	validator, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, providerAddr)
	if !found {
		return stakingtypes.ErrNoValidatorFound
	}

	// check if the consumer chain is registered, i.e.,
	// a client to the consumer was already created
	_, consumerRegistered := k.GetConsumerClientId(ctx, chainID)

	// get the previous key assigned for this validator on this consumer chain
	oldConsumerKey, found := k.GetValidatorConsumerPubKey(ctx, chainID, providerAddr)
	if !found {
		// the validator had no key assigned on this consumer chain
		providerKey, err := validator.TmConsPublicKey()
		if err != nil {
			return err
		}
		oldConsumerKey = providerKey
	} else {
		if consumerRegistered {
			// mark this old consumer key as prunable once the VSCMaturedPacket
			// for the current VSC ID is received;
			// note: this state is removed on receiving the VSCMaturedPacket
			k.AppendConsumerValidatorByVscID(
				ctx,
				chainID,
				k.GetValidatorSetUpdateId(ctx),
				utils.TMCryptoPublicKeyToConsAddr(oldConsumerKey),
			)
		}
	}

	// get the previous power of this validator
	oldPower := k.stakingKeeper.GetLastValidatorPower(ctx, sdk.ValAddress(validator.OperatorAddress))
	// if the validator is active and the consumer is registered,
	// then store old key and power for modifying the valset update in EndBlock;
	// note: this state is deleted at the end of the block
	if oldPower > 0 && consumerRegistered {
		k.SetPendingKeyAssignment(
			ctx,
			chainID,
			providerAddr,
			abci.ValidatorUpdate{PubKey: oldConsumerKey, Power: oldPower},
		)
	}

	// set the mapping from this validator's provider address to the new consumer key;
	// overwrite if already exists
	// note: this state is deleted when the validator is removed from the staking module
	k.SetValidatorConsumerPubKey(ctx, chainID, providerAddr, consumerKey)

	// if the consumer chain is already registered, set the mapping from
	// this validator's new consensus address on the consumer
	// to its consensus address on the provider;
	// otherwise, the mapping is added when the consumer is registered
	if consumerRegistered {
		consumerAddr := utils.TMCryptoPublicKeyToConsAddr(consumerKey)
		if _, found := k.GetValidatorByConsumerAddr(ctx, chainID, consumerAddr); found {
			// mapping already exists; return error
			return sdkerrors.Wrapf(
				types.ErrInvalidConsumerConsensusPubKey, "consumer key already exists",
			)
		}
		// note: this state must be deleted through the pruning mechanism;
		// see ConsumerValidatorsByVscID
		k.SetValidatorByConsumerAddr(ctx, chainID, consumerAddr, providerAddr)
	}

	return nil
}

// PruneKeyAssignments prunes the consumer addresses no longer needed
// as they cannot be referenced in slash requests (by a correct consumer)
func (k Keeper) PruneKeyAssignments(ctx sdk.Context, chainID string, vscID uint64) {
	consumerAddrs := k.GetConsumerValidatorByVscID(ctx, chainID, vscID)
	for _, addr := range consumerAddrs {
		k.DeleteValidatorByConsumerAddr(ctx, chainID, addr)
	}
	k.DeleteConsumerValidatorByVscID(ctx, chainID, vscID)
}
