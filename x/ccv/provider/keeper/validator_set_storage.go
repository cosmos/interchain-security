package keeper

import (
	"fmt"

	"cosmossdk.io/math"
	storetypes "cosmossdk.io/store/types"

	sdk "github.com/cosmos/cosmos-sdk/types"

	"github.com/cosmos/interchain-security/v7/x/ccv/provider/types"
)

// The functions here are meant to provide a generic interface to a validator set that
// is stored under a certain prefix.
// It is used to store the validator set for the consumer chain and the last validator set
// sent to the consensus engine on the provider; see
// provider_consensus.go and validator_set_update.go

// GetValidatorKey constructs the key to access a given validator, stored under a given prefix.
// This method is public for testing.
func GetValidatorKey(prefix []byte, providerConsAddr types.ProviderConsAddress) []byte {
	return append(prefix, providerConsAddr.ToSdkConsAddr()...)
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
		return fmt.Errorf("marshalling ConsensusValidator: %w", err)
	}

	store.Set(GetValidatorKey(prefix, types.NewProviderConsAddress(validator.ProviderConsAddr)), bz)
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

// deleteValidator removes validator with `providerConsAddr` address from the
// validator set stored under the given prefix.
func (k Keeper) deleteValidator(
	ctx sdk.Context,
	prefix []byte,
	providerConsAddr types.ProviderConsAddress,
) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(GetValidatorKey(prefix, providerConsAddr))
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

// isValidator returns `true` if the validator with `providerConsAddr` exists
// in the validator set stored under the given prefix.
func (k Keeper) isValidator(ctx sdk.Context, prefix []byte, providerConsAddr types.ProviderConsAddress) bool {
	store := ctx.KVStore(k.storeKey)
	return store.Get(GetValidatorKey(prefix, providerConsAddr)) != nil
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
			return validators, fmt.Errorf("unmarshalling ConsensusValidator: %w", err)
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
		return totalPower, err
	}
	for _, val := range validators {
		totalPower = totalPower.Add(math.NewInt(val.Power))
	}
	return totalPower, nil
}
