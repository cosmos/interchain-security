package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"

	"github.com/cosmos/interchain-security/x/ccv/provider/types"

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

// AppendConsumerValidatorByVscID appends a consumer validator address to the list of ValidatorByConsumerAddr
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
