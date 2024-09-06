package keeper

import (
	"encoding/binary"
	"errors"
	"fmt"

	errorsmod "cosmossdk.io/errors"
	storetypes "cosmossdk.io/store/types"

	sdk "github.com/cosmos/cosmos-sdk/types"

	"github.com/cosmos/interchain-security/v6/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v6/x/ccv/types"
)

// GetConsumerPowerShapingParameters returns the power-shaping parameters associated with this consumer id
func (k Keeper) GetConsumerPowerShapingParameters(ctx sdk.Context, consumerId string) (types.PowerShapingParameters, error) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerIdToPowerShapingParametersKey(consumerId))
	if bz == nil {
		return types.PowerShapingParameters{}, errorsmod.Wrapf(ccvtypes.ErrStoreKeyNotFound,
			"GetConsumerPowerShapingParameters, consumerId(%s)", consumerId)
	}
	var parameters types.PowerShapingParameters
	if err := parameters.Unmarshal(bz); err != nil {
		return types.PowerShapingParameters{}, errorsmod.Wrapf(ccvtypes.ErrStoreUnmarshal,
			"GetConsumerPowerShapingParameters, consumerId(%s): %s", consumerId, err.Error())
	}
	return parameters, nil
}

// SetConsumerPowerShapingParameters sets the power-shaping parameters associated with this consumer id.
// Note that it also updates the allowlist and denylist indexes if they are different
func (k Keeper) SetConsumerPowerShapingParameters(ctx sdk.Context, consumerId string, parameters types.PowerShapingParameters) error {
	store := ctx.KVStore(k.storeKey)
	bz, err := parameters.Marshal()
	if err != nil {
		return fmt.Errorf("failed to marshal power-shaping parameters (%+v) for consumer id (%s): %w", parameters, consumerId, err)
	}

	// get old power shaping params
	oldParameters, err := k.GetConsumerPowerShapingParameters(ctx, consumerId)
	// ignore ErrStoreKeyNotFound errors as this might be the first time the power shaping params are set
	if errors.Is(err, ccvtypes.ErrStoreUnmarshal) {
		return fmt.Errorf("cannot get consumer previous power shaping parameters: %w", err)
	}

	store.Set(types.ConsumerIdToPowerShapingParametersKey(consumerId), bz)

	// update allowlist and denylist indexes if needed
	if !equalStringSlices(oldParameters.Allowlist, parameters.Allowlist) {
		k.UpdateAllowlist(ctx, consumerId, parameters.Allowlist)
	}
	if !equalStringSlices(oldParameters.Denylist, parameters.Denylist) {
		k.UpdateDenylist(ctx, consumerId, parameters.Denylist)
	}

	return nil
}

// equalStringSlices returns true if two string slices are equal
func equalStringSlices(a, b []string) bool {
	if len(a) != len(b) {
		return false
	}
	for i, v := range a {
		if v != b[i] {
			return false
		}
	}
	return true
}

// SetAllowlist allowlists validator with `providerAddr` address on chain `consumerId`
func (k Keeper) SetAllowlist(
	ctx sdk.Context,
	consumerId string,
	providerAddr types.ProviderConsAddress,
) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.AllowlistKey(consumerId, providerAddr), []byte{})
}

// GetAllowList returns all allowlisted validators
func (k Keeper) GetAllowList(
	ctx sdk.Context,
	consumerId string,
) (providerConsAddresses []types.ProviderConsAddress) {
	store := ctx.KVStore(k.storeKey)
	key := types.StringIdWithLenKey(types.AllowlistKeyPrefix(), consumerId)
	iterator := storetypes.KVStorePrefixIterator(store, key)
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		providerConsAddresses = append(providerConsAddresses, types.NewProviderConsAddress(iterator.Key()[len(key):]))
	}

	return providerConsAddresses
}

// IsAllowlisted returns `true` if validator with `providerAddr` has been allowlisted on chain `consumerId`
func (k Keeper) IsAllowlisted(
	ctx sdk.Context,
	consumerId string,
	providerAddr types.ProviderConsAddress,
) bool {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.AllowlistKey(consumerId, providerAddr))
	return bz != nil
}

// DeleteAllowlist deletes all allowlisted validators
func (k Keeper) DeleteAllowlist(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	iterator := storetypes.KVStorePrefixIterator(store, types.StringIdWithLenKey(types.AllowlistKeyPrefix(), consumerId))
	defer iterator.Close()

	keysToDel := [][]byte{}
	for ; iterator.Valid(); iterator.Next() {
		keysToDel = append(keysToDel, iterator.Key())
	}

	for _, key := range keysToDel {
		store.Delete(key)
	}
}

// IsAllowlistEmpty returns `true` if no validator is allowlisted on chain `consumerId`
func (k Keeper) IsAllowlistEmpty(ctx sdk.Context, consumerId string) bool {
	store := ctx.KVStore(k.storeKey)
	iterator := storetypes.KVStorePrefixIterator(store, types.StringIdWithLenKey(types.AllowlistKeyPrefix(), consumerId))
	defer iterator.Close()

	return !iterator.Valid()
}

// UpdateAllowlist populates the allowlist store for the consumer chain with this consumer id
func (k Keeper) UpdateAllowlist(ctx sdk.Context, consumerId string, allowlist []string) {
	k.DeleteAllowlist(ctx, consumerId)
	for _, address := range allowlist {
		consAddr, err := sdk.ConsAddressFromBech32(address)
		if err != nil {
			continue
		}

		k.SetAllowlist(ctx, consumerId, types.NewProviderConsAddress(consAddr))
	}
}

// SetDenylist denylists validator with `providerAddr` address on chain `consumerId`
func (k Keeper) SetDenylist(
	ctx sdk.Context,
	consumerId string,
	providerAddr types.ProviderConsAddress,
) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.DenylistKey(consumerId, providerAddr), []byte{})
}

// GetDenyList returns all denylisted validators
func (k Keeper) GetDenyList(
	ctx sdk.Context,
	consumerId string,
) (providerConsAddresses []types.ProviderConsAddress) {
	store := ctx.KVStore(k.storeKey)
	key := types.StringIdWithLenKey(types.DenylistKeyPrefix(), consumerId)
	iterator := storetypes.KVStorePrefixIterator(store, key)
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		providerConsAddresses = append(providerConsAddresses, types.NewProviderConsAddress(iterator.Key()[len(key):]))
	}

	return providerConsAddresses
}

// IsDenylisted returns `true` if validator with `providerAddr` has been denylisted on chain `consumerId`
func (k Keeper) IsDenylisted(
	ctx sdk.Context,
	consumerId string,
	providerAddr types.ProviderConsAddress,
) bool {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.DenylistKey(consumerId, providerAddr))
	return bz != nil
}

// DeleteDenylist deletes all denylisted validators
func (k Keeper) DeleteDenylist(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	iterator := storetypes.KVStorePrefixIterator(store, types.StringIdWithLenKey(types.DenylistKeyPrefix(), consumerId))
	defer iterator.Close()

	keysToDel := [][]byte{}
	for ; iterator.Valid(); iterator.Next() {
		keysToDel = append(keysToDel, iterator.Key())
	}

	for _, key := range keysToDel {
		store.Delete(key)
	}
}

// IsDenylistEmpty returns `true` if no validator is denylisted on chain `consumerId`
func (k Keeper) IsDenylistEmpty(ctx sdk.Context, consumerId string) bool {
	store := ctx.KVStore(k.storeKey)
	iterator := storetypes.KVStorePrefixIterator(store, types.StringIdWithLenKey(types.DenylistKeyPrefix(), consumerId))
	defer iterator.Close()

	return !iterator.Valid()
}

// UpdateDenylist populates the denylist store for the consumer chain with this consumer id
func (k Keeper) UpdateDenylist(ctx sdk.Context, consumerId string, denylist []string) {
	k.DeleteDenylist(ctx, consumerId)
	for _, address := range denylist {
		consAddr, err := sdk.ConsAddressFromBech32(address)
		if err != nil {
			continue
		}

		k.SetDenylist(ctx, consumerId, types.NewProviderConsAddress(consAddr))
	}
}

// SetMinimumPowerInTopN sets the minimum power required for a validator to be in the top N
// for a given consumer chain.
func (k Keeper) SetMinimumPowerInTopN(
	ctx sdk.Context,
	consumerId string,
	power int64,
) {
	store := ctx.KVStore(k.storeKey)

	buf := make([]byte, 8)
	binary.BigEndian.PutUint64(buf, uint64(power))

	store.Set(types.MinimumPowerInTopNKey(consumerId), buf)
}

// GetMinimumPowerInTopN returns the minimum power required for a validator to be in the top N
// for a given consumer chain.
func (k Keeper) GetMinimumPowerInTopN(
	ctx sdk.Context,
	consumerId string,
) (int64, bool) {
	store := ctx.KVStore(k.storeKey)
	buf := store.Get(types.MinimumPowerInTopNKey(consumerId))
	if buf == nil {
		return 0, false
	}
	return int64(binary.BigEndian.Uint64(buf)), true
}

// DeleteMinimumPowerInTopN removes the minimum power required for a validator to be in the top N
// for a given consumer chain.
func (k Keeper) DeleteMinimumPowerInTopN(
	ctx sdk.Context,
	consumerId string,
) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.MinimumPowerInTopNKey(consumerId))
}

// UpdateMinimumPowerInTopN populates the minimum power in Top N for the consumer chain with this consumer id
func (k Keeper) UpdateMinimumPowerInTopN(ctx sdk.Context, consumerId string, oldTopN, newTopN uint32) error {
	// if the top N changes, we need to update the new minimum power in top N
	if newTopN != oldTopN {
		if newTopN > 0 {
			// if the chain receives a non-zero top N value, store the minimum power in the top N
			bondedValidators, err := k.GetLastProviderConsensusActiveValidators(ctx)
			if err != nil {
				return err
			}
			minPower, err := k.ComputeMinPowerInTopN(ctx, bondedValidators, newTopN)
			if err != nil {
				return err
			}
			k.SetMinimumPowerInTopN(ctx, consumerId, minPower)
		} else {
			// if the chain receives a zero top N value, we delete the min power
			k.DeleteMinimumPowerInTopN(ctx, consumerId)
		}
	}

	return nil
}
