package keeper

import (
	"bytes"
	"encoding/binary"
	"encoding/gob"
	"fmt"
	"strconv"
	"time"

	errorsmod "cosmossdk.io/errors"
	storetypes "cosmossdk.io/store/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
)

// ConsumerPhase captures the phases of a consumer chain according to `docs/docs/adrs/adr-018-permissionless-ics.md`
type ConsumerPhase byte

const (
	// Registered phase indicates the phase in which a consumer chain has been assigned a unique consumer id. This consumer
	// id can be used to interact with the consumer chain (e.g., when a validator opts in to a chain). A chain in this
	// phase cannot yet launch. It has to be initialized first.
	Registered ConsumerPhase = iota
	// Initialized phase indicates the phase in which a consumer chain has set all the needed parameters to launch but
	// has not yet launched (e.g., because the `spawnTime` of the consumer chain has not yet been reached).
	Initialized
	// FailedToLaunch phase indicates that the chain attempted but failed to launch (e.g., due to no validator opting in).
	FailedToLaunch
	// Launched phase corresponds to the phase in which a consumer chain is running and consuming a subset of the validator
	// set of the provider.
	Launched
	// Stopped phase corresponds to the phase in which a previously-launched chain has stopped.
	Stopped
)

// setConsumerId sets the provided consumerId
func (k Keeper) setConsumerId(ctx sdk.Context, consumerId uint64) {
	store := ctx.KVStore(k.storeKey)

	buf := make([]byte, 8)
	binary.BigEndian.PutUint64(buf, consumerId)

	store.Set(types.ConsumerIdKey(), buf)
}

// GetConsumerId returns the last registered consumer id
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
func (k Keeper) SetConsumerInitializationParameters(ctx sdk.Context, consumerId string, record types.ConsumerInitializationParameters) error {
	store := ctx.KVStore(k.storeKey)
	bz, err := record.Marshal()
	if err != nil {
		return fmt.Errorf("failed to marshal initialization record (%+v) for consumer id (%s): %w", record, consumerId, err)
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
func (k Keeper) GetConsumerPhase(ctx sdk.Context, consumerId string) (ConsumerPhase, bool) {
	store := ctx.KVStore(k.storeKey)
	buf := store.Get(types.ConsumerIdToPhaseKey(consumerId))
	if buf == nil {
		return ConsumerPhase(0), false
	}
	return ConsumerPhase(buf[0]), true
}

// SetConsumerPhase sets the phase associated with this consumer id
// TODO (PERMISSIONLESS): use this method when launching and when stopping a chain
func (k Keeper) SetConsumerPhase(ctx sdk.Context, consumerId string, phase ConsumerPhase) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.ConsumerIdToPhaseKey(consumerId), []byte{byte(phase)})
}

// DeleteConsumerPhase deletes the phase associated with this consumer id
func (k Keeper) DeleteConsumerPhase(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerIdToPhaseKey(consumerId))
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

// GetConsumersToBeLaunched
func (k Keeper) GetConsumersToBeLaunched(ctx sdk.Context, spawnTime time.Time) (types.ConsumerIds, error) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.SpawnTimeToConsumerIdsKey(spawnTime))
	if bz == nil {
		return types.ConsumerIds{}, nil
	}

	var consumerIds types.ConsumerIds

	if err := consumerIds.Unmarshal(bz); err != nil {
		return types.ConsumerIds{}, fmt.Errorf("failed to unmarshal consumer ids: %w", err)
	}
	return consumerIds, nil
}

// AppendSpawnTimeForConsumerToBeLaunched
func (k Keeper) AppendSpawnTimeForConsumerToBeLaunched(ctx sdk.Context, consumerId string, spawnTime time.Time) error {
	store := ctx.KVStore(k.storeKey)

	consumerIdsSlice, err := k.GetConsumersToBeLaunched(ctx, spawnTime)
	if err != nil {
		return err
	}
	consumerIds := append(consumerIdsSlice.Ids, consumerId)

	appendedConsumerIdsStr := types.ConsumerIds{
		Ids: consumerIds,
	}

	bz, err := appendedConsumerIdsStr.Marshal()
	if err != nil {
		return err
	}

	store.Set(types.SpawnTimeToConsumerIdsKey(spawnTime), bz)
	return nil
}

// RemoveConsumerFromToBeLaunchedConsumers
func (k Keeper) RemoveConsumerFromToBeLaunchedConsumers(ctx sdk.Context, consumerId string, spawnTime time.Time) error {
	store := ctx.KVStore(k.storeKey)

	consumerIds, err := k.GetConsumersToBeLaunched(ctx, spawnTime)
	if err != nil {
		return err
	}

	if len(consumerIds.Ids) == 0 {
		return fmt.Errorf("no consumer ids for spawn time: %s", spawnTime.String())
	}

	// find the index of the consumer we want to remove
	index := 0
	for i := 0; i < len(consumerIds.Ids); i = i + 1 {
		if consumerIds.Ids[i] == consumerId {
			index = i
			break
		}
	}
	if consumerIds.Ids[index] != consumerId {
		return fmt.Errorf("failed to find consumer id (%s) in the chains to be launched", consumerId)
	}

	if len(consumerIds.Ids) == 1 {
		store.Delete(types.SpawnTimeToConsumerIdsKey(spawnTime))
		return nil
	}

	updatedConsumerIds := append(consumerIds.Ids[:index], consumerIds.Ids[index+1:]...)

	updatedConsumerIdsStr := types.ConsumerIds{
		Ids: updatedConsumerIds,
	}

	bz, err := updatedConsumerIdsStr.Marshal()
	if err != nil {
		return err
	}

	store.Set(types.SpawnTimeToConsumerIdsKey(spawnTime), bz)
	return nil
}

// TODO (PERMISSIONLESS) merge the functions, they practically do the same

// GetConsumersToBeStopped
func (k Keeper) GetConsumersToBeStopped(ctx sdk.Context, stopTime time.Time) (types.ConsumerIds, error) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.StopTimeToConsumerIdsKey(stopTime))
	if bz == nil {
		return types.ConsumerIds{}, nil
	}

	var consumerIds types.ConsumerIds
	err := consumerIds.Unmarshal(bz)
	if err != nil {
		return types.ConsumerIds{}, err
	}
	return consumerIds, nil
}

// AppendSpawnTimeForConsumerToBeStopped
func (k Keeper) AppendStopTimeForConsumerToBeStopped(ctx sdk.Context, consumerId string, stopTime time.Time) error {
	store := ctx.KVStore(k.storeKey)

	consumerIdsStr, err := k.GetConsumersToBeStopped(ctx, stopTime)
	if err != nil {
		return err
	}
	consumerIds := append(consumerIdsStr.Ids, consumerId)

	consumerIdsNewStr := types.ConsumerIds{
		Ids: consumerIds,
	}

	bz, err := consumerIdsNewStr.Marshal()
	if err != nil {
		return err
	}

	store.Set(types.StopTimeToConsumerIdsKey(stopTime), bz)
	return nil
}

// RemoveConsumerFromToBeStoppedConsumers
func (k Keeper) RemoveConsumerFromToBeStoppedConsumers(ctx sdk.Context, consumerId string, stopTime time.Time) error {
	store := ctx.KVStore(k.storeKey)

	consumerIds, err := k.GetConsumersToBeStopped(ctx, stopTime)
	if err != nil {
		return err
	}

	if len(consumerIds.Ids) == 0 {
		return fmt.Errorf("no consumer ids for stop time: %s", stopTime.String())
	}

	// find the index of the consumer we want to remove
	index := 0
	for i := 0; i < len(consumerIds.Ids); i = i + 1 {
		if consumerIds.Ids[i] == consumerId {
			index = i
			break
		}
	}
	if consumerIds.Ids[index] != consumerId {
		return fmt.Errorf("failed to find consumer id (%s) in the chains to be stopped", consumerId)
	}

	if len(consumerIds.Ids) == 1 {
		store.Delete(types.StopTimeToConsumerIdsKey(stopTime))
		return nil
	}

	updatedConsumerIds := append(consumerIds.Ids[:index], consumerIds.Ids[index+1:]...)
	updatedConsumerIdsStr := types.ConsumerIds{
		Ids: updatedConsumerIds,
	}
	bz, err := updatedConsumerIdsStr.Marshal()
	if err != nil {
		return err
	}

	store.Set(types.StopTimeToConsumerIdsKey(stopTime), bz)
	return nil
}

// GetOptedInConsumerIds
func (k Keeper) GetOptedInConsumerIds(ctx sdk.Context, providerAddr types.ProviderConsAddress) ([]string, error) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ProviderConsAddrToOptedInConsumerIdsKey(providerAddr))
	if bz == nil {
		return []string{}, nil
	}

	var consumerIds []string
	buf := bytes.NewBuffer(bz)
	dec := gob.NewDecoder(buf)
	err := dec.Decode(&consumerIds)
	return consumerIds, err
}

// AppendOptedInConsumerId
func (k Keeper) AppendOptedInConsumerId(ctx sdk.Context, providerAddr types.ProviderConsAddress, consumerId string) error {
	store := ctx.KVStore(k.storeKey)

	consumerIds, err := k.GetOptedInConsumerIds(ctx, providerAddr)
	if err != nil {
		return err
	}
	consumerIds = append(consumerIds, consumerId)

	var buf bytes.Buffer
	enc := gob.NewEncoder(&buf)
	err = enc.Encode(consumerIds)
	if err != nil {
		return err
	}

	store.Set(types.ProviderConsAddrToOptedInConsumerIdsKey(providerAddr), buf.Bytes())
	return nil
}

// RemoveOptedInConsumerId
func (k Keeper) RemoveOptedInConsumerId(ctx sdk.Context, providerAddr types.ProviderConsAddress, consumerId string) error {
	store := ctx.KVStore(k.storeKey)

	consumerIds, err := k.GetOptedInConsumerIds(ctx, providerAddr)
	if err != nil {
		return err
	}

	if len(consumerIds) == 0 {
		return fmt.Errorf("no consumer ids for provider consensus address: %s", providerAddr.String())
	}

	// find the index of the consumer we want to remove
	index := 0
	for i := 0; i < len(consumerIds); i = i + 1 {
		if consumerIds[i] == consumerId {
			index = i
			break
		}
	}
	if consumerIds[index] != consumerId {
		return fmt.Errorf("failed to find consumer id (%s) from the opted-in chains", consumerId)
	}

	if len(consumerIds) == 1 {
		store.Delete(types.ProviderConsAddrToOptedInConsumerIdsKey(providerAddr))
		return nil
	}

	updatedConsumerIds := append(consumerIds[:index], consumerIds[index+1:]...)
	var buf bytes.Buffer
	enc := gob.NewEncoder(&buf)
	err = enc.Encode(updatedConsumerIds)
	if err != nil {
		return err
	}

	store.Set(types.ProviderConsAddrToOptedInConsumerIdsKey(providerAddr), buf.Bytes())
	return nil
}

// GetClientIdToConsumerId returns the consumer id associated with this client id
func (k Keeper) GetClientIdToConsumerId(ctx sdk.Context, clientId string) (string, bool) {
	store := ctx.KVStore(k.storeKey)
	buf := store.Get(types.ClientIdToConsumerIdKey(clientId))
	if buf == nil {
		return "", false
	}
	return string(buf), true
}

// SetClientIdToConsumerId sets the client id associated with this consumer id
func (k Keeper) SetClientIdToConsumerId(ctx sdk.Context, clientId string, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.ClientIdToConsumerIdKey(clientId), []byte(consumerId))
}

// DeleteClientIdToConsumerId deletes the client id to consumer id association
func (k Keeper) DeleteClientIdToConsumerId(ctx sdk.Context, clientId string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ClientIdToConsumerIdKey(clientId))
}

// GetInitializedConsumersReadyToLaunch returns the consumer ids of the pending initialized consumer chains
// that are ready to launch,  i.e., consumer clients to be created.
func (k Keeper) GetInitializedConsumersReadyToLaunch(ctx sdk.Context, limit uint32) []string {
	store := ctx.KVStore(k.storeKey)

	spawnTimeToConsumerIdsKeyPrefix := types.SpawnTimeToConsumerIdsKeyPrefix()
	iterator := storetypes.KVStorePrefixIterator(store, []byte{spawnTimeToConsumerIdsKeyPrefix})
	defer iterator.Close()

	result := []string{}
	for ; iterator.Valid(); iterator.Next() {
		spawnTime, err := types.ParseTime(types.SpawnTimeToConsumerIdsKeyPrefix(), iterator.Key())
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

// TODO: @sainoe merge with func above
func (k Keeper) GetInitializedConsumers(ctx sdk.Context) []string {
	store := ctx.KVStore(k.storeKey)

	spawnTimeToConsumerIdsKeyPrefix := types.SpawnTimeToConsumerIdsKeyPrefix()
	iterator := storetypes.KVStorePrefixIterator(store, []byte{spawnTimeToConsumerIdsKeyPrefix})
	defer iterator.Close()

	result := []string{}
	for ; iterator.Valid(); iterator.Next() {
		spawnTime, err := types.ParseTime(types.SpawnTimeToConsumerIdsKeyPrefix(), iterator.Key())
		if err != nil {
			k.Logger(ctx).Error("failed to parse spawn time",
				"error", err)
			continue
		}

		// if current block time is equal to or after spawnTime, and the chain is initialized, we can launch the chain
		consumerIds, err := k.GetConsumersToBeLaunched(ctx, spawnTime)
		if err != nil {
			k.Logger(ctx).Error("failed to retrieve consumers to launch",
				"spawn time", spawnTime,
				"error", err)
			continue
		}

		result = append(result, consumerIds.Ids...)
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
		return errorsmod.Wrapf(types.ErrNoConsumerGenesis, "consumer genesis could not be found")
	}

	if len(consumerGenesis.Provider.InitialValSet) == 0 {
		return errorsmod.Wrapf(types.ErrInvalidConsumerGenesis, "consumer genesis initial validator set is empty - no validators opted in")
	}

	// The cached context is created with a new EventManager so we merge the event
	// into the original context
	ctx.EventManager().EmitEvents(ctx.EventManager().Events())
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

// GetLaunchedConsumersReadyToStop returns the consumer ids of the pending launched consumer chains
// that are ready to stop
func (k Keeper) GetLaunchedConsumersReadyToStop(ctx sdk.Context, limit uint32) []string {
	store := ctx.KVStore(k.storeKey)

	stopTimeToConsumerIdsKeyPrefix := types.StopTimeToConsumerIdsKeyPrefix()
	iterator := storetypes.KVStorePrefixIterator(store, []byte{stopTimeToConsumerIdsKeyPrefix})
	defer iterator.Close()

	result := []string{}
	for ; iterator.Valid(); iterator.Next() {
		stopTime, err := types.ParseTime(types.StopTimeToConsumerIdsKeyPrefix(), iterator.Key())
		if err != nil {
			k.Logger(ctx).Error("failed to parse stop time",
				"error", err)
			continue
		}
		if stopTime.After(ctx.BlockTime()) {
			return result
		}

		consumerIds, err := k.GetConsumersToBeStopped(ctx, stopTime)
		if err != nil {
			k.Logger(ctx).Error("failed to retrieve consumers to stop",
				"stop time", stopTime,
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

// IsValidatorOptedInToChainId checks if the validator with `providerAddr` is opted into the chain with the specified `chainId`.
// It returns `found == true` and the corresponding chain's `consumerId` if the validator is opted in. Otherwise, it returns an empty string
// for `consumerId` and `found == false`.
func (k Keeper) IsValidatorOptedInToChainId(ctx sdk.Context, providerAddr types.ProviderConsAddress, chainId string) (string, bool) {
	consumerIds, err := k.GetOptedInConsumerIds(ctx, providerAddr)
	if err != nil {
		k.Logger(ctx).Error("failed to retrieve the consumer ids this validator is opted in to",
			"providerAddr", providerAddr,
			"error", err)
		return "", false
	}

	for _, consumerId := range consumerIds {
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

func (k Keeper) PrepareConsumerForLaunch(ctx sdk.Context, consumerId string, previousSpawnTime time.Time, spawnTime time.Time) {
	if !previousSpawnTime.Equal(time.Time{}) {
		// if this is not the first initialization and hence `previousSpawnTime` does not contain the zero value of `Time`
		// remove the consumer id from the old spawn time
		k.RemoveConsumerFromToBeLaunchedConsumers(ctx, consumerId, previousSpawnTime)
	}
	k.AppendSpawnTimeForConsumerToBeLaunched(ctx, consumerId, spawnTime)
}

// CanLaunch checks on whether the consumer with `consumerId` has set all the initialization parameters set and hence
// is ready to launch and at what spawn time
// TODO (PERMISSIONLESS): could remove, all fields should be there because we validate the initialization parameters
func (k Keeper) CanLaunch(ctx sdk.Context, consumerId string) (time.Time, bool) {
	// a chain that is already launched or stopped cannot launch again
	phase, found := k.GetConsumerPhase(ctx, consumerId)
	if !found || phase == Launched || phase == Stopped {
		return time.Time{}, false
	}

	initializationParameters, err := k.GetConsumerInitializationParameters(ctx, consumerId)
	if err != nil {
		return time.Time{}, false
	}

	// a chain can only launch if the spawn time is in the future
	spawnTimeInTheFuture := initializationParameters.SpawnTime.After(ctx.BlockTime())

	genesisHashSet := initializationParameters.GenesisHash != nil
	binaryHashSet := initializationParameters.BinaryHash != nil

	consumerRedistributionFractionSet := initializationParameters.ConsumerRedistributionFraction != ""
	blocksPerDistributionTransmissionSet := initializationParameters.BlocksPerDistributionTransmission > 0
	historicalEntriesSet := initializationParameters.HistoricalEntries > 0

	return initializationParameters.SpawnTime, spawnTimeInTheFuture && genesisHashSet && binaryHashSet && consumerRedistributionFractionSet &&
		blocksPerDistributionTransmissionSet && historicalEntriesSet
}
