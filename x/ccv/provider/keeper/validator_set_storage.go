package keeper

import (
	"fmt"

	"cosmossdk.io/math"
	sdk "github.com/cosmos/cosmos-sdk/types"

	"github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
)

// getValidatorKey constructs the key to access a given validator, stored under a given prefix.
func (k Keeper) getValidatorKey(prefix []byte, providerAddr types.ProviderConsAddress) []byte {
	return append(prefix, providerAddr.ToSdkConsAddr()...)
}

// setValidator stores the given `validator` in the validator set stored under the given prefix.
func (k Keeper) setValidator(
	ctx sdk.Context,
	prefix []byte,
	validator types.ConsumerValidator,
) {
	store := ctx.KVStore(k.storeKey)
	bz, err := validator.Marshal()
	if err != nil {
		panic(fmt.Errorf("failed to marshal ConsumerValidator: %w", err))
	}

	store.Set(k.getValidatorKey(prefix, types.NewProviderConsAddress(validator.ProviderConsAddr)), bz)
}

// setValSet resets the validator set stored under the given prefix to the provided `nextValidators`.
func (k Keeper) setValSet(ctx sdk.Context, prefix []byte, nextValidators []types.ConsumerValidator) {
	k.deleteValSet(ctx, prefix)
	for _, val := range nextValidators {
		k.setValidator(ctx, prefix, val)
	}
}

// deleteValidator removes validator with `providerAddr` address from the
// validator set stored under the given prefix.
func (k Keeper) deleteValidator(
	ctx sdk.Context,
	prefix []byte,
	providerConsAddr types.ProviderConsAddress,
) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(k.getValidatorKey(prefix, providerConsAddr))
}

// deleteValSet deletes all the stored consumer validators under the given prefix.
func (k Keeper) deleteValSet(
	ctx sdk.Context,
	prefix []byte,
) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, prefix)

	var keysToDel [][]byte
	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		keysToDel = append(keysToDel, iterator.Key())
	}
	for _, delKey := range keysToDel {
		store.Delete(delKey)
	}
}

// isValidator returns `true` if the validator with `providerAddr` exists
// in the validator set stored under the given prefix.
func (k Keeper) isValidator(ctx sdk.Context, prefix []byte, providerAddr types.ProviderConsAddress) bool {
	store := ctx.KVStore(k.storeKey)
	return store.Get(k.getValidatorKey(prefix, providerAddr)) != nil
}

// getValSet returns all the validators stored under the given prefix.
func (k Keeper) getValSet(
	ctx sdk.Context,
	key []byte,
) (validators []types.ConsumerValidator) {
	store := ctx.KVStore(k.storeKey)
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

func (k Keeper) getTotalPower(ctx sdk.Context, prefix []byte) math.Int {
	var totalPower math.Int
	validators := k.getValSet(ctx, prefix)
	for _, val := range validators {
		totalPower = totalPower.Add(math.NewInt(val.Power))
	}
	return totalPower
}
