package keeper

import (
	"fmt"

	"cosmossdk.io/math"
	storetypes "cosmossdk.io/store/types"
	sdk "github.com/cosmos/cosmos-sdk/types"

	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
)

// getValidatorKey constructs the key to access a given validator, stored under a given prefix.
func (k Keeper) getValidatorKey(prefix []byte, providerAddr types.ProviderConsAddress) []byte {
	return append(prefix, providerAddr.ToSdkConsAddr()...)
}

// setValidator stores the given `validator` in the validator set stored under the given prefix.
func (k Keeper) setValidator(
	ctx sdk.Context,
	prefix []byte,
	validator types.ConsensusValidator,
) error {
	store := ctx.KVStore(k.storeKey)
	bz, err := validator.Marshal()
	if err != nil {
		return fmt.Errorf("marshalling ConsumerValidator: %w", err)
	}

	store.Set(k.getValidatorKey(prefix, types.NewProviderConsAddress(validator.ProviderConsAddr)), bz)
	return nil
}

// setValSet resets the validator set stored under the given prefix to the provided `nextValidators`.
func (k Keeper) setValSet(ctx sdk.Context, prefix []byte, nextValidators []types.ConsensusValidator) error {
	k.deleteValSet(ctx, prefix)
	for _, val := range nextValidators {
		err := k.setValidator(ctx, prefix, val)
		if err != nil {
			return err
		}
	}
	return nil
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
	iterator := storetypes.KVStorePrefixIterator(store, prefix)

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
	prefix []byte,
) (validators []types.ConsensusValidator, err error) {
	store := ctx.KVStore(k.storeKey)
	iterator := storetypes.KVStorePrefixIterator(store, prefix)
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		iterator.Value()
		var validator types.ConsensusValidator
		if err := validator.Unmarshal(iterator.Value()); err != nil {
			return validators, fmt.Errorf("unmarshalling ConsumerValidator: %w", err)
		}
		validators = append(validators, validator)
	}

	return validators, err
}

// getTotalPower computes the total power of all the consumer validators stored under the given prefix.
func (k Keeper) getTotalPower(ctx sdk.Context, prefix []byte) (math.Int, error) {
	totalPower := math.ZeroInt()
	validators, err := k.getValSet(ctx, prefix)
	if err != nil {
		panic(fmt.Errorf("retrieving validator set: %w", err))
	}
	for _, val := range validators {
		totalPower = totalPower.Add(math.NewInt(val.Power))
	}
	return totalPower, nil
}
