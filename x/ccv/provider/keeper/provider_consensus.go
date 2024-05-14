package keeper

import (
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"

	"github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
)

// SetLastProviderConsensusValidator sets the given validator to be stored
// as part of the last provider consensus validator set
func (k Keeper) SetLastProviderConsensusValidator(
	ctx sdk.Context,
	validator types.ConsumerValidator,
) {
	store := ctx.KVStore(k.storeKey)
	bz, err := validator.Marshal()
	if err != nil {
		panic(fmt.Errorf("failed to marshal ConsumerValidator: %w", err))
	}

	store.Set(types.LastProviderConsensusValidatorKey(validator.ProviderConsAddr), bz)
}

// SetLastProviderConsensusValSet resets the stored last validator set sent to the consensus engine on the provider
// to the provided nextValidators.
func (k Keeper) SetLastProviderConsensusValSet(ctx sdk.Context, nextValidators []types.ConsumerValidator) {
	k.DeleteLastProviderConsensusValSet(ctx)
	for _, val := range nextValidators {
		k.SetLastProviderConsensusValidator(ctx, val)
	}
}

// DeleteLastProviderConsensusValidator removes the validator with `providerConsAddr` address
// from the stored last provider consensus validator set
func (k Keeper) DeleteLastProviderConsensusValidator(
	ctx sdk.Context,
	providerConsAddr types.ProviderConsAddress,
) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.LastProviderConsensusValidatorKey(providerConsAddr.ToSdkConsAddr()))
}

// DeleteLastProviderConsensusValSet deletes all the stored validators from the
// last provider consensus validator set
func (k Keeper) DeleteLastProviderConsensusValSet(
	ctx sdk.Context,
) {
	store := ctx.KVStore(k.storeKey)
	key := []byte{types.LastProviderConsensusValsPrefix}
	iterator := sdk.KVStorePrefixIterator(store, key)

	var keysToDel [][]byte
	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		keysToDel = append(keysToDel, iterator.Key())
	}
	for _, delKey := range keysToDel {
		store.Delete(delKey)
	}
}

// GetLastProviderConsensusValSet returns the last stored
// validator set sent to the consensus engine on the provider
func (k Keeper) GetLastProviderConsensusValSet(
	ctx sdk.Context,
) (validators []types.ConsumerValidator) {
	store := ctx.KVStore(k.storeKey)
	key := []byte{types.LastProviderConsensusValsPrefix}
	iterator := sdk.KVStorePrefixIterator(store, key)
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		iterator.Value()
		var validator types.ConsumerValidator
		if err := validator.Unmarshal(iterator.Value()); err != nil {
			panic(fmt.Errorf("failed to unmarshal ConsumerValidator: %w", err))
		}
		validators = append(validators, validator)
	}

	return validators
}
