package keeper

import (
	"encoding/binary"
	"fmt"
	"strconv"
	"time"

	errorsmod "cosmossdk.io/errors"
	storetypes "cosmossdk.io/store/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	govv1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1"
	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
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
		return types.PowerShapingParameters{}, fmt.Errorf("failed to retrieve power-shaping parameters for consumer id (%s)", consumerId)
	}
	var record types.PowerShapingParameters
	if err := record.Unmarshal(bz); err != nil {
		return types.PowerShapingParameters{}, fmt.Errorf("failed to unmarshal power-shaping parameters for consumer id (%s): %w", consumerId, err)
	}
	return record, nil
}

// SetConsumerPowerShapingParameters sets the power-shaping parameters associated with this consumer id
func (k Keeper) SetConsumerPowerShapingParameters(ctx sdk.Context, consumerId string, parameters types.PowerShapingParameters) error {
	store := ctx.KVStore(k.storeKey)
	bz, err := parameters.Marshal()
	if err != nil {
		return fmt.Errorf("failed to marshal power-shaping parameters (%+v) for consumer id (%s): %w", parameters, consumerId, err)
	}
	store.Set(types.ConsumerIdToPowerShapingParametersKey(consumerId), bz)
	return nil
}

// DeleteConsumerPowerShapingParameters deletes the power-shaping parameters associated with this consumer id
func (k Keeper) DeleteConsumerPowerShapingParameters(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerIdToPowerShapingParametersKey(consumerId))
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

// GetConsumerStopTime returns the stop time associated with the to-be-stopped chain with consumer id
func (k Keeper) GetConsumerStopTime(ctx sdk.Context, consumerId string) (time.Time, error) {
	store := ctx.KVStore(k.storeKey)
	buf := store.Get(types.ConsumerIdToStopTimeKey(consumerId))
	if buf == nil {
		return time.Time{}, fmt.Errorf("failed to retrieve stop time for consumer id (%s)", consumerId)
	}
	var time time.Time
	if err := time.UnmarshalBinary(buf); err != nil {
		return time, fmt.Errorf("failed to unmarshal stop time for consumer id (%s): %w", consumerId, err)
	}
	return time, nil
}

// SetConsumerStopTime sets the stop time associated with this consumer id
func (k Keeper) SetConsumerStopTime(ctx sdk.Context, consumerId string, stopTime time.Time) error {
	store := ctx.KVStore(k.storeKey)
	buf, err := stopTime.MarshalBinary()
	if err != nil {
		return fmt.Errorf("failed to marshal stop time (%+v) for consumer id (%s): %w", stopTime, consumerId, err)
	}
	store.Set(types.ConsumerIdToStopTimeKey(consumerId), buf)
	return nil
}

// DeleteConsumerStopTime deletes the stop time associated with this consumer id
func (k Keeper) DeleteConsumerStopTime(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerIdToStopTimeKey(consumerId))
}

// getConsumerIdsBasedOnTime returns all the consumer ids stored under this specific `key(time)`
func (k Keeper) getConsumerIdsBasedOnTime(ctx sdk.Context, key func(time.Time) []byte, time time.Time) (types.ConsumerIds, error) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(key(time))
	if bz == nil {
		return types.ConsumerIds{}, nil
	}

	var consumerIds types.ConsumerIds

	if err := consumerIds.Unmarshal(bz); err != nil {
		return types.ConsumerIds{}, fmt.Errorf("failed to unmarshal consumer ids: %w", err)
	}
	return consumerIds, nil
}

// appendConsumerIdOnTime appends the consumer id on all the other consumer ids under `key(time)`
func (k Keeper) appendConsumerIdOnTime(ctx sdk.Context, consumerId string, key func(time.Time) []byte, time time.Time) error {
	store := ctx.KVStore(k.storeKey)

	consumers, err := k.getConsumerIdsBasedOnTime(ctx, key, time)
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

	store.Set(key(time), bz)
	return nil
}

// removeConsumerIdFromTime removes consumer id stored under `key(time)`
func (k Keeper) removeConsumerIdFromTime(ctx sdk.Context, consumerId string, key func(time.Time) []byte, time time.Time) error {
	store := ctx.KVStore(k.storeKey)

	consumers, err := k.getConsumerIdsBasedOnTime(ctx, key, time)
	if err != nil {
		return err
	}

	if len(consumers.Ids) == 0 {
		return fmt.Errorf("no consumer ids found for this time: %s", time.String())
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
		store.Delete(key(time))
		return nil
	}

	consumersWithRemoval := types.ConsumerIds{
		Ids: append(consumers.Ids[:index], consumers.Ids[index+1:]...),
	}

	bz, err := consumersWithRemoval.Marshal()
	if err != nil {
		return err
	}

	store.Set(key(time), bz)
	return nil
}

// GetConsumersToBeLaunched returns all the consumer ids of chains stored under this spawn time
func (k Keeper) GetConsumersToBeLaunched(ctx sdk.Context, spawnTime time.Time) (types.ConsumerIds, error) {
	return k.getConsumerIdsBasedOnTime(ctx, types.SpawnTimeToConsumerIdsKey, spawnTime)
}

// AppendConsumerToBeLaunched appends the provider consumer id for the given spawn time
func (k Keeper) AppendConsumerToBeLaunched(ctx sdk.Context, consumerId string, spawnTime time.Time) error {
	return k.appendConsumerIdOnTime(ctx, consumerId, types.SpawnTimeToConsumerIdsKey, spawnTime)
}

// RemoveConsumerToBeLaunched removes consumer id from if stored for this specific spawn time
func (k Keeper) RemoveConsumerToBeLaunched(ctx sdk.Context, consumerId string, spawnTime time.Time) error {
	return k.removeConsumerIdFromTime(ctx, consumerId, types.SpawnTimeToConsumerIdsKey, spawnTime)
}

// GetConsumersToBeStopped returns all the consumer ids of chains stored under this stop time
func (k Keeper) GetConsumersToBeStopped(ctx sdk.Context, stopTime time.Time) (types.ConsumerIds, error) {
	return k.getConsumerIdsBasedOnTime(ctx, types.StopTimeToConsumerIdsKey, stopTime)
}

// AppendConsumerToBeStopped appends the provider consumer id for the given stop time
func (k Keeper) AppendConsumerToBeStopped(ctx sdk.Context, consumerId string, stopTime time.Time) error {
	return k.appendConsumerIdOnTime(ctx, consumerId, types.StopTimeToConsumerIdsKey, stopTime)
}

// RemoveConsumerToBeStopped removes consumer id from if stored for this specific stop time
func (k Keeper) RemoveConsumerToBeStopped(ctx sdk.Context, consumerId string, stopTime time.Time) error {
	return k.removeConsumerIdFromTime(ctx, consumerId, types.StopTimeToConsumerIdsKey, stopTime)
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

// GetConsumersReadyToLaunch returns the consumer ids of the pending initialized consumer chains
// that are ready to launch,  i.e., consumer clients to be created.
func (k Keeper) GetConsumersReadyToLaunch(ctx sdk.Context, limit uint32) []string {
	store := ctx.KVStore(k.storeKey)

	spawnTimeToConsumerIdsKeyPrefix := types.SpawnTimeToConsumerIdsKeyPrefix()
	iterator := storetypes.KVStorePrefixIterator(store, []byte{spawnTimeToConsumerIdsKeyPrefix})
	defer iterator.Close()

	result := []string{}
	for ; iterator.Valid(); iterator.Next() {
		spawnTime, err := types.ParseTime(spawnTimeToConsumerIdsKeyPrefix, iterator.Key())
		if err != nil {
			k.Logger(ctx).Error("failed to parse spawn time",
				"error", err)
			continue
		}
		if spawnTime.After(ctx.BlockTime()) {
			return result
		}

		// if current block time is equal to or after spawnTime, and the chain is initialized, we can launch the chain
		consumerIds, err := k.GetConsumersToBeLaunched(ctx, spawnTime)
		if err != nil {
			k.Logger(ctx).Error("failed to retrieve consumers to launch",
				"spawn time", spawnTime,
				"error", err)
			continue
		}
		if len(result)+len(consumerIds.Ids) >= int(limit) {
			remainingConsumerIds := len(result) + len(consumerIds.Ids) - int(limit)
			if len(consumerIds.Ids[:len(consumerIds.Ids)-remainingConsumerIds]) == 0 {
				return result
			}
			return append(result, consumerIds.Ids[:len(consumerIds.Ids)-remainingConsumerIds]...)
		} else {
			result = append(result, consumerIds.Ids...)
		}
	}

	return result
}

// GetConsumersReadyToStop returns the consumer ids of the pending launched consumer chains
// that are ready to stop
func (k Keeper) GetConsumersReadyToStop(ctx sdk.Context, limit uint32) []string {
	store := ctx.KVStore(k.storeKey)

	stopTimeToConsumerIdsKeyPrefix := types.StopTimeToConsumerIdsKeyPrefix()
	iterator := storetypes.KVStorePrefixIterator(store, []byte{stopTimeToConsumerIdsKeyPrefix})
	defer iterator.Close()

	result := []string{}
	for ; iterator.Valid(); iterator.Next() {
		stopTime, err := types.ParseTime(stopTimeToConsumerIdsKeyPrefix, iterator.Key())
		if err != nil {
			k.Logger(ctx).Error("failed to parse stop time",
				"error", err)
			continue
		}
		if stopTime.After(ctx.BlockTime()) {
			return result
		}

		consumers, err := k.GetConsumersToBeStopped(ctx, stopTime)
		if err != nil {
			k.Logger(ctx).Error("failed to retrieve consumers to stop",
				"stop time", stopTime,
				"error", err)
			continue
		}
		if len(result)+len(consumers.Ids) >= int(limit) {
			remainingConsumerIds := len(result) + len(consumers.Ids) - int(limit)
			if len(consumers.Ids[:len(consumers.Ids)-remainingConsumerIds]) == 0 {
				return result
			}
			return append(result, consumers.Ids[:len(consumers.Ids)-remainingConsumerIds]...)
		} else {
			result = append(result, consumers.Ids...)
		}
	}

	return result
}

// LaunchConsumer launches the chain with the provided consumer id by creating the consumer client and the respective
// consumer genesis file
func (k Keeper) LaunchConsumer(ctx sdk.Context, consumerId string) error {
	err := k.CreateConsumerClient(ctx, consumerId)
	if err != nil {
		return err
	}

	consumerGenesis, found := k.GetConsumerGenesis(ctx, consumerId)
	if !found {
		return errorsmod.Wrapf(types.ErrNoConsumerGenesis, "consumer genesis could not be found for consumer id: %s", consumerId)
	}

	if len(consumerGenesis.Provider.InitialValSet) == 0 {
		return errorsmod.Wrapf(types.ErrInvalidConsumerGenesis, "consumer genesis initial validator set is empty - no validators opted in consumer id: %s", consumerId)
	}

	return nil
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

// UpdateMinimumPowerInTopN populates the minimum power in Top N for the consumer chain with this consumer id
func (k Keeper) UpdateMinimumPowerInTopN(ctx sdk.Context, consumerId string, oldTopN uint32, newTopN uint32) error {
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

// PrepareConsumerForLaunch prepares to move the launch of a consumer chain from the previous spawn time to spawn time.
// Previous spawn time can correspond to its zero value if the validator was not previously set for launch.
func (k Keeper) PrepareConsumerForLaunch(ctx sdk.Context, consumerId string, previousSpawnTime time.Time, spawnTime time.Time) error {
	if !previousSpawnTime.Equal(time.Time{}) {
		// if this is not the first initialization and hence `previousSpawnTime` does not contain the zero value of `Time`
		// remove the consumer id from the previous spawn time
		err := k.RemoveConsumerToBeLaunched(ctx, consumerId, previousSpawnTime)
		if err != nil {
			return err
		}
	}
	return k.AppendConsumerToBeLaunched(ctx, consumerId, spawnTime)
}

// CanLaunch checks on whether the consumer with `consumerId` has set all the initialization parameters set and hence
// is ready to launch and at what spawn time
// TODO (PERMISSIONLESS): could remove, all fields should be there because we validate the initialization parameters
func (k Keeper) CanLaunch(ctx sdk.Context, consumerId string) (time.Time, bool) {
	// a chain that is already launched or stopped cannot launch again
	phase := k.GetConsumerPhase(ctx, consumerId)
	if phase == types.ConsumerPhase_CONSUMER_PHASE_LAUNCHED || phase == types.ConsumerPhase_CONSUMER_PHASE_STOPPED {
		return time.Time{}, false
	}

	initializationParameters, err := k.GetConsumerInitializationParameters(ctx, consumerId)
	if err != nil {
		return time.Time{}, false
	}

	spawnTimeIsNotZero := !initializationParameters.SpawnTime.Equal(time.Time{})

	genesisHashSet := initializationParameters.GenesisHash != nil
	binaryHashSet := initializationParameters.BinaryHash != nil

	consumerRedistributionFractionSet := initializationParameters.ConsumerRedistributionFraction != ""
	blocksPerDistributionTransmissionSet := initializationParameters.BlocksPerDistributionTransmission > 0
	historicalEntriesSet := initializationParameters.HistoricalEntries > 0

	return initializationParameters.SpawnTime, spawnTimeIsNotZero && genesisHashSet && binaryHashSet && consumerRedistributionFractionSet &&
		blocksPerDistributionTransmissionSet && historicalEntriesSet
}

// HasAtMostOnceCorrectMsgUpdateConsumer checks that the proposal has at most one `MsgUpdateConsumer` that is
// correctly set (i.e., the owner address of the to-be-updated consumer corresponds to the gov module). Returns
// the single `MsgUpdateConsumer` message if only one correctly set exists.
func (k Keeper) HasAtMostOnceCorrectMsgUpdateConsumer(ctx sdk.Context, proposal *govv1.Proposal) (*types.MsgUpdateConsumer, error) {
	var msgUpdateConsumer *types.MsgUpdateConsumer
	for _, msg := range proposal.GetMessages() {
		sdkMsg, isMsgUpdateConsumer := msg.GetCachedValue().(*types.MsgUpdateConsumer)
		if isMsgUpdateConsumer {
			// A `MsgUpdateConsumer` can only succeed if the owner of the consumer chain is the gov module.
			// If that's not the case, we immediately fail the proposal.
			// Note that someone could potentially change the owner of a chain to be that of the gov module
			// while a proposal is active and before the proposal is executed. Even then, we still do not allow
			// `MsgUpdateConsumer` proposals if the owner of the chain is not the gov module to avoid someone forgetting
			// to change the owner address while the proposal is active.
			ownerAddress, err := k.GetConsumerOwnerAddress(ctx, sdkMsg.ConsumerId)
			if err != nil {
				return nil, fmt.Errorf("cannot find owner address for consumer with consumer id (%s): %s", sdkMsg.ConsumerId, err.Error())
			} else if ownerAddress != k.GetAuthority() {
				return nil, fmt.Errorf("owner address (%s) is not the gov module (%s)", ownerAddress, k.GetAuthority())
			}

			if msgUpdateConsumer != nil {
				return nil, fmt.Errorf("proposal can contain at most one `MsgUpdateConsumer` message")
			}
			msgUpdateConsumer = sdkMsg
		}
	}
	return msgUpdateConsumer, nil
}

// DoesNotHaveDeprecatedMessage checks that the provided proposal does not contain any deprecated messages and returns
// an error if this is the case
func DoesNotHaveDeprecatedMessage(proposal *govv1.Proposal) error {
	for _, msg := range proposal.GetMessages() {
		// if the proposal contains a deprecated message, cancel the proposal
		_, isMsgConsumerAddition := msg.GetCachedValue().(*types.MsgConsumerAddition)
		if isMsgConsumerAddition {
			return fmt.Errorf("proposal cannot contain deprecated `MsgConsumerAddition`; use `MsgCreateConsumer` instead")
		}
		_, isMsgConsumerModification := msg.GetCachedValue().(*types.MsgConsumerModification)
		if isMsgConsumerModification {
			return fmt.Errorf("proposal cannot contain deprecated `MsgConsumerModification`; use `MsgUpdateConsumer` instead")
		}
		_, isMsgConsumerRemoval := msg.GetCachedValue().(*types.MsgConsumerRemoval)
		if isMsgConsumerRemoval {
			return fmt.Errorf("proposal cannot contain deprecated `MsgConsumerRemoval`; use `MsgRemoveConsumer` instead")
		}
	}
	return nil
}
