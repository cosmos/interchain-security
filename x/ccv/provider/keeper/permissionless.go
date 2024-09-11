package keeper

import (
	"encoding/binary"
	"fmt"
	"strconv"

	sdk "github.com/cosmos/cosmos-sdk/types"

	"github.com/cosmos/interchain-security/v6/x/ccv/provider/types"
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
func (k Keeper) SetConsumerChainId(ctx sdk.Context, consumerId, chainId string) {
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
func (k Keeper) SetConsumerOwnerAddress(ctx sdk.Context, consumerId, chainId string) {
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
	var initializationParameters types.ConsumerInitializationParameters
	if err := initializationParameters.Unmarshal(bz); err != nil {
		return types.ConsumerInitializationParameters{}, fmt.Errorf("failed to unmarshal initialization parameters for consumer id (%s): %w", consumerId, err)
	}
	return initializationParameters, nil
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

// GetConsumerPhase returns the phase associated with this consumer id
func (k Keeper) GetConsumerPhase(ctx sdk.Context, consumerId string) types.ConsumerPhase {
	store := ctx.KVStore(k.storeKey)
	buf := store.Get(types.ConsumerIdToPhaseKey(consumerId))
	if buf == nil {
		return types.CONSUMER_PHASE_UNSPECIFIED
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
	return phase == types.CONSUMER_PHASE_REGISTERED ||
		phase == types.CONSUMER_PHASE_INITIALIZED ||
		phase == types.CONSUMER_PHASE_LAUNCHED
}
