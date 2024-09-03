package keeper

import (
	"encoding/binary"
	"errors"
	"fmt"
	"strconv"

	errorsmod "cosmossdk.io/errors"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v5/x/ccv/types"
)

// setConsumerId sets the provided consumerId
func (k Keeper) setConsumerId(ctx sdk.Context, consumerId uint64) {
	store := ctx.KVStore(k.storeKey)

	buf := make([]byte, 8)
	binary.BigEndian.PutUint64(buf, consumerId)

	store.Set(types.ConsumerIdKey(), buf)
}

// GetConsumerId returns the next to-be-assigned consumer id
func (k Keeper) GetConsumerId(ctx sdk.Context) (uint64, bool) {
	store := ctx.KVStore(k.storeKey)
	buf := store.Get(types.ConsumerIdKey())
	if buf == nil {
		return 0, false
	}
	return binary.BigEndian.Uint64(buf), true
}

// FetchAndIncrementConsumerId fetches the first consumer id that can be used and increments the
// underlying consumer id
func (k Keeper) FetchAndIncrementConsumerId(ctx sdk.Context) string {
	consumerId, _ := k.GetConsumerId(ctx)
	k.setConsumerId(ctx, consumerId+1)
	return strconv.FormatUint(consumerId, 10)
}

// GetConsumerChainId returns the chain id associated with this consumer id
func (k Keeper) GetConsumerChainId(ctx sdk.Context, consumerId string) (string, error) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerIdToChainIdKey(consumerId))
	if bz == nil {
		return "", fmt.Errorf("failed to retrieve chain id for consumer id (%s)", consumerId)
	}
	return string(bz), nil
}

// SetConsumerChainId sets the chain id associated with this consumer id
func (k Keeper) SetConsumerChainId(ctx sdk.Context, consumerId string, chainId string) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.ConsumerIdToChainIdKey(consumerId), []byte(chainId))
}

// DeleteConsumerChainId deletes the chain id associated with this consumer id
func (k Keeper) DeleteConsumerChainId(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerIdToChainIdKey(consumerId))
}

// GetConsumerOwnerAddress returns the owner address associated with this consumer id
func (k Keeper) GetConsumerOwnerAddress(ctx sdk.Context, consumerId string) (string, error) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerIdToOwnerAddressKey(consumerId))
	if bz == nil {
		return "", fmt.Errorf("failed to retrieve owner address for consumer id (%s)", consumerId)
	}
	return string(bz), nil
}

// SetConsumerOwnerAddress sets the chain id associated with this consumer id
func (k Keeper) SetConsumerOwnerAddress(ctx sdk.Context, consumerId string, chainId string) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.ConsumerIdToOwnerAddressKey(consumerId), []byte(chainId))
}

// DeleteConsumerOwnerAddress deletes the owner address associated with this consumer id
func (k Keeper) DeleteConsumerOwnerAddress(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerIdToOwnerAddressKey(consumerId))
}

// GetConsumerMetadata returns the registration record associated with this consumer id
func (k Keeper) GetConsumerMetadata(ctx sdk.Context, consumerId string) (types.ConsumerMetadata, error) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerIdToMetadataKey(consumerId))
	if bz == nil {
		return types.ConsumerMetadata{}, fmt.Errorf("failed to retrieve metadata for consumer id (%s)", consumerId)
	}
	var metadata types.ConsumerMetadata
	if err := metadata.Unmarshal(bz); err != nil {
		return types.ConsumerMetadata{}, fmt.Errorf("failed to unmarshal metadata for consumer id (%s): %w", consumerId, err)
	}
	return metadata, nil
}

// SetConsumerMetadata sets the registration record associated with this consumer id
func (k Keeper) SetConsumerMetadata(ctx sdk.Context, consumerId string, metadata types.ConsumerMetadata) error {
	store := ctx.KVStore(k.storeKey)
	bz, err := metadata.Marshal()
	if err != nil {
		return fmt.Errorf("failed to marshal registration metadata (%+v) for consumer id (%s): %w", metadata, consumerId, err)
	}
	store.Set(types.ConsumerIdToMetadataKey(consumerId), bz)
	return nil
}

// DeleteConsumerMetadata deletes the metadata associated with this consumer id
func (k Keeper) DeleteConsumerMetadata(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerIdToMetadataKey(consumerId))
}

// GetConsumerInitializationParameters returns the initialization parameters associated with this consumer id
func (k Keeper) GetConsumerInitializationParameters(ctx sdk.Context, consumerId string) (types.ConsumerInitializationParameters, error) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerIdToInitializationParametersKey(consumerId))
	if bz == nil {
		return types.ConsumerInitializationParameters{}, fmt.Errorf("failed to retrieve initialization parameters for consumer id (%s)", consumerId)
	}
	var record types.ConsumerInitializationParameters
	if err := record.Unmarshal(bz); err != nil {
		return types.ConsumerInitializationParameters{}, fmt.Errorf("failed to unmarshal stop time for consumer id (%s): %w", consumerId, err)
	}
	return record, nil
}

// SetConsumerInitializationParameters sets the initialization parameters associated with this consumer id
func (k Keeper) SetConsumerInitializationParameters(ctx sdk.Context, consumerId string, parameters types.ConsumerInitializationParameters) error {
	store := ctx.KVStore(k.storeKey)
	bz, err := parameters.Marshal()
	if err != nil {
		return fmt.Errorf("failed to marshal initialization parameters (%+v) for consumer id (%s): %w", parameters, consumerId, err)
	}
	store.Set(types.ConsumerIdToInitializationParametersKey(consumerId), bz)
	return nil
}

// DeleteConsumerInitializationParameters deletes the initialization parameters associated with this consumer id
func (k Keeper) DeleteConsumerInitializationParameters(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerIdToInitializationParametersKey(consumerId))
}

// GetConsumerPowerShapingParameters returns the power-shaping parameters associated with this consumer id
func (k Keeper) GetConsumerPowerShapingParameters(ctx sdk.Context, consumerId string) (types.PowerShapingParameters, error) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerIdToPowerShapingParametersKey(consumerId))
	if bz == nil {
		return types.PowerShapingParameters{}, errorsmod.Wrapf(ccvtypes.ErrStoreKeyNotFound,
			"GetConsumerPowerShapingParameters, consumerId(%s)", consumerId)
	}
	var record types.PowerShapingParameters
	if err := record.Unmarshal(bz); err != nil {
		return types.PowerShapingParameters{}, errorsmod.Wrapf(ccvtypes.ErrStoreUnmarshal,
			"GetConsumerPowerShapingParameters, consumerId(%s): %s", consumerId, err.Error())
	}
	return record, nil
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

// GetConsumerPhase returns the phase associated with this consumer id
func (k Keeper) GetConsumerPhase(ctx sdk.Context, consumerId string) types.ConsumerPhase {
	store := ctx.KVStore(k.storeKey)
	buf := store.Get(types.ConsumerIdToPhaseKey(consumerId))
	if buf == nil {
		return types.ConsumerPhase_CONSUMER_PHASE_UNSPECIFIED
	}
	phase := types.ConsumerPhase(binary.BigEndian.Uint32(buf))
	return phase
}

// SetConsumerPhase sets the phase associated with this consumer id
func (k Keeper) SetConsumerPhase(ctx sdk.Context, consumerId string, phase types.ConsumerPhase) {
	store := ctx.KVStore(k.storeKey)
	phaseBytes := make([]byte, 8)
	binary.BigEndian.PutUint32(phaseBytes, uint32(phase))
	store.Set(types.ConsumerIdToPhaseKey(consumerId), phaseBytes)
}

// DeleteConsumerPhase deletes the phase associated with this consumer id
func (k Keeper) DeleteConsumerPhase(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerIdToPhaseKey(consumerId))
}

// IsConsumerActive checks if a consumer chain is either registered, initialized, or launched.
func (k Keeper) IsConsumerActive(ctx sdk.Context, consumerId string) bool {
	phase := k.GetConsumerPhase(ctx, consumerId)
	return phase == types.ConsumerPhase_CONSUMER_PHASE_REGISTERED ||
		phase == types.ConsumerPhase_CONSUMER_PHASE_INITIALIZED ||
		phase == types.ConsumerPhase_CONSUMER_PHASE_LAUNCHED
}

// GetOptedInConsumerIds returns all the consumer ids where the given validator is opted in
func (k Keeper) GetOptedInConsumerIds(ctx sdk.Context, providerAddr types.ProviderConsAddress) (types.ConsumerIds, error) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ProviderConsAddrToOptedInConsumerIdsKey(providerAddr))
	if bz == nil {
		return types.ConsumerIds{}, nil
	}

	var consumerIds types.ConsumerIds
	if err := consumerIds.Unmarshal(bz); err != nil {
		return types.ConsumerIds{}, fmt.Errorf("failed to unmarshal consumer ids: %w", err)
	}

	return consumerIds, nil
}

// AppendOptedInConsumerId appends given consumer id to the list of consumers that validator has opted in
// TODO (PERMISSIONLESS) -- combine it with SetOptedIn
func (k Keeper) AppendOptedInConsumerId(ctx sdk.Context, providerAddr types.ProviderConsAddress, consumerId string) error {
	store := ctx.KVStore(k.storeKey)

	consumers, err := k.GetOptedInConsumerIds(ctx, providerAddr)
	if err != nil {
		return err
	}

	consumersWithAppend := types.ConsumerIds{
		Ids: append(consumers.Ids, consumerId),
	}

	bz, err := consumersWithAppend.Marshal()
	if err != nil {
		return err
	}

	store.Set(types.ProviderConsAddrToOptedInConsumerIdsKey(providerAddr), bz)
	return nil
}

// RemoveOptedInConsumerId removes the consumer id from this validator because it is not opted in anymore
func (k Keeper) RemoveOptedInConsumerId(ctx sdk.Context, providerAddr types.ProviderConsAddress, consumerId string) error {
	store := ctx.KVStore(k.storeKey)

	consumers, err := k.GetOptedInConsumerIds(ctx, providerAddr)
	if err != nil {
		return err
	}

	if len(consumers.Ids) == 0 {
		return fmt.Errorf("no consumer ids found for this provviderAddr: %s", providerAddr.String())
	}

	// find the index of the consumer we want to remove
	index := -1
	for i := 0; i < len(consumers.Ids); i = i + 1 {
		if consumers.Ids[i] == consumerId {
			index = i
			break
		}
	}

	if index == -1 {
		return fmt.Errorf("failed to find consumer id (%s)", consumerId)
	}

	if len(consumers.Ids) == 1 {
		store.Delete(types.ProviderConsAddrToOptedInConsumerIdsKey(providerAddr))
		return nil
	}

	consumersWithRemoval := types.ConsumerIds{
		Ids: append(consumers.Ids[:index], consumers.Ids[index+1:]...),
	}

	bz, err := consumersWithRemoval.Marshal()
	if err != nil {
		return err
	}

	store.Set(types.ProviderConsAddrToOptedInConsumerIdsKey(providerAddr), bz)
	return nil
}

// IsValidatorOptedInToChainId checks if the validator with `providerAddr` is opted into the chain with the specified `chainId`.
// It returns `found == true` and the corresponding chain's `consumerId` if the validator is opted in. Otherwise, it returns an empty string
// for `consumerId` and `found == false`.
func (k Keeper) IsValidatorOptedInToChainId(ctx sdk.Context, providerAddr types.ProviderConsAddress, chainId string) (string, bool) {
	consumers, err := k.GetOptedInConsumerIds(ctx, providerAddr)
	if err != nil {
		k.Logger(ctx).Error("failed to retrieve the consumer ids this validator is opted in to",
			"providerAddr", providerAddr,
			"error", err)
		return "", false
	}

	for _, consumerId := range consumers.Ids {
		consumerChainId, err := k.GetConsumerChainId(ctx, consumerId)
		if err != nil {
			k.Logger(ctx).Error("cannot find chain id",
				"consumerId", consumerId,
				"error", err)
			continue
		}

		if consumerChainId == chainId {
			return consumerId, true
		}

	}
	return "", false
}
