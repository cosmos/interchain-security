package keeper

import (
	"bytes"
	errorsmod "cosmossdk.io/errors"
	storetypes "cosmossdk.io/store/types"
	"encoding/binary"
	"encoding/gob"
	"fmt"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	"sort"
	"strconv"
	"time"
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
	// TODO (PERMISSIONLESS) add this if the chain fails to launch
	// Useful so we do not keep trying to launch failed chains
	// FailedToLaunch phase indicates that the chain attempted but failed to launch (e.g., due to no validator opting in)
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

// getConsumerId returns the last registered consumer id
func (k Keeper) getConsumerId(ctx sdk.Context) (uint64, bool) {
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
	consumerId, _ := k.getConsumerId(ctx)
	k.setConsumerId(ctx, consumerId+1)
	return strconv.FormatUint(consumerId, 10)
}

// GetConsumerRegistrationRecord returns the registration record associated with this consumer id
func (k Keeper) GetConsumerRegistrationRecord(ctx sdk.Context, consumerId string) (types.ConsumerRegistrationRecord, error) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerIdToRegistrationRecordKey(consumerId))
	if bz == nil {
		return types.ConsumerRegistrationRecord{}, fmt.Errorf("failed to retrieve registration record for consumer id (%s)", consumerId)
	}
	var record types.ConsumerRegistrationRecord
	if err := record.Unmarshal(bz); err != nil {
		return types.ConsumerRegistrationRecord{}, fmt.Errorf("failed to unmarshal registration record for consumer id (%s): %w", consumerId, err)
	}
	return record, nil
}

// SetConsumerRegistrationRecord sets the registration record associated with this consumer id
func (k Keeper) SetConsumerRegistrationRecord(ctx sdk.Context, consumerId string, record types.ConsumerRegistrationRecord) error {
	store := ctx.KVStore(k.storeKey)
	bz, err := record.Marshal()
	if err != nil {
		return fmt.Errorf("failed to marshal registration record (%+v) for consumer id (%s): %w", record, consumerId, err)
	}
	store.Set(types.ConsumerIdToRegistrationRecordKey(consumerId), bz)
	return nil
}

// DeleteConsumerRegistrationRecord deletes the registration record associated with this consumer id
func (k Keeper) DeleteConsumerRegistrationRecord(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerIdToRegistrationRecordKey(consumerId))
}

// GetConsumerInitializationRecord returns the initialization record associated with this consumer id
func (k Keeper) GetConsumerInitializationRecord(ctx sdk.Context, consumerId string) (types.ConsumerInitializationRecord, error) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerIdToInitializationRecordKey(consumerId))
	if bz == nil {
		return types.ConsumerInitializationRecord{}, fmt.Errorf("failed to retrieve initialization record for consumer id (%s)", consumerId)
	}
	var record types.ConsumerInitializationRecord
	if err := record.Unmarshal(bz); err != nil {
		return types.ConsumerInitializationRecord{}, fmt.Errorf("failed to unmarshal stop time for consumer id (%s): %w", consumerId, err)
	}
	return record, nil
}

// SetConsumerInitializationRecord sets the initialization record associated with this consumer id
func (k Keeper) SetConsumerInitializationRecord(ctx sdk.Context, consumerId string, record types.ConsumerInitializationRecord) error {
	store := ctx.KVStore(k.storeKey)
	bz, err := record.Marshal()
	if err != nil {
		return fmt.Errorf("failed to marshal initialization record (%+v) for consumer id (%s): %w", record, consumerId, err)
	}
	store.Set(types.ConsumerIdToInitializationRecordKey(consumerId), bz)
	return nil
}

// DeleteConsumerInitializationRecord deletes the initialization record associated with this consumer id
func (k Keeper) DeleteConsumerInitializationRecord(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerIdToInitializationRecordKey(consumerId))
}

// GetConsumerUpdateRecord returns the update record associated with this consumer id
func (k Keeper) GetConsumerUpdateRecord(ctx sdk.Context, consumerId string) (types.ConsumerUpdateRecord, error) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerIdToUpdateRecordKey(consumerId))
	if bz == nil {
		return types.ConsumerUpdateRecord{}, fmt.Errorf("failed to retrieve update record for consumer id (%s)", consumerId)
	}
	var record types.ConsumerUpdateRecord
	if err := record.Unmarshal(bz); err != nil {
		return types.ConsumerUpdateRecord{}, fmt.Errorf("failed to unmarshal update record for consumer id (%s): %w", consumerId, err)
	}
	return record, nil
}

// SetConsumerUpdateRecord sets the update record associated with this consumer id
func (k Keeper) SetConsumerUpdateRecord(ctx sdk.Context, consumerId string, record types.ConsumerUpdateRecord) error {
	store := ctx.KVStore(k.storeKey)
	bz, err := record.Marshal()
	if err != nil {
		return fmt.Errorf("failed to marshal update record (%+v) for consumer id (%s): %w", record, consumerId, err)
	}
	store.Set(types.ConsumerIdToUpdateRecordKey(consumerId), bz)
	return nil
}

// DeleteConsumerUpdateRecord deletes the update record associated with this consumer id
func (k Keeper) DeleteConsumerUpdateRecord(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerIdToUpdateRecordKey(consumerId))
}

// GetConsumerOwnerAddress returns the owner address associated with this consumer id
func (k Keeper) GetConsumerOwnerAddress(ctx sdk.Context, consumerId string) string {
	updateRecord, _ := k.GetConsumerUpdateRecord(ctx, consumerId)
	return updateRecord.OwnerAddress
}

// SetConsumerOwnerAddress sets the owner address associated with this consumer id
func (k Keeper) SetConsumerOwnerAddress(ctx sdk.Context, consumerId string, ownerAddress string) {
	updateRecord, _ := k.GetConsumerUpdateRecord(ctx, consumerId)
	updateRecord.OwnerAddress = ownerAddress
	k.SetConsumerUpdateRecord(ctx, consumerId, updateRecord)
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
func (k Keeper) GetConsumersToBeLaunched(ctx sdk.Context, spawnTime time.Time) ([]string, error) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.SpawnTimeToConsumerIdsKey(spawnTime))
	if bz == nil {
		return []string{}, nil
	}

	var consumerIds []string
	buf := bytes.NewBuffer(bz)
	dec := gob.NewDecoder(buf)
	err := dec.Decode(&consumerIds)
	return consumerIds, err
}

// AppendSpawnTimeForConsumerToBeLaunched
func (k Keeper) AppendSpawnTimeForConsumerToBeLaunched(ctx sdk.Context, consumerId string, spawnTime time.Time) error {
	store := ctx.KVStore(k.storeKey)

	consumerIds, err := k.GetConsumersToBeLaunched(ctx, spawnTime)
	if err != nil {
		return err
	}
	consumerIds = append(consumerIds, consumerId)

	// sort so that we avoid getting a consumer id in front of everyone else and delaying the appending of a chain
	sort.Slice(consumerIds, func(i, j int) bool {
		return consumerIds[i] < consumerIds[j]
	})

	var buf bytes.Buffer
	enc := gob.NewEncoder(&buf)
	err = enc.Encode(consumerIds)
	if err != nil {
		return err
	}

	store.Set(types.SpawnTimeToConsumerIdsKey(spawnTime), buf.Bytes())
	return nil
}

// RemoveConsumerFromToBeLaunchedConsumers
func (k Keeper) RemoveConsumerFromToBeLaunchedConsumers(ctx sdk.Context, consumerId string, spawnTime time.Time) error {
	store := ctx.KVStore(k.storeKey)

	consumerIds, err := k.GetConsumersToBeLaunched(ctx, spawnTime)
	if err != nil {
		return err
	}

	if len(consumerIds) == 0 {
		return fmt.Errorf("no consumer ids for spawn time: %s", spawnTime.String())
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
		return fmt.Errorf("failed to find consumer id (%s) in the chains to be launched", consumerId)
	}

	if len(consumerIds) == 1 {
		store.Delete(types.SpawnTimeToConsumerIdsKey(spawnTime))
		return nil
	}

	updatedConsumerIds := append(consumerIds[:index], consumerIds[index+1:]...)
	var buf bytes.Buffer
	enc := gob.NewEncoder(&buf)
	err = enc.Encode(updatedConsumerIds)
	if err != nil {
		return err
	}

	store.Set(types.SpawnTimeToConsumerIdsKey(spawnTime), buf.Bytes())
	return nil
}

// TODO (PERMISSIONLESS) merge the functions, they practicall do the same

// GetConsumersToBeStopped
func (k Keeper) GetConsumersToBeStopped(ctx sdk.Context, stopTime time.Time) ([]string, error) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.StopTimeToConsumerIdsKey(stopTime))
	if bz == nil {
		return []string{}, nil
	}

	var consumerIds []string
	buf := bytes.NewBuffer(bz)
	dec := gob.NewDecoder(buf)
	err := dec.Decode(&consumerIds)
	return consumerIds, err
}

// AppendSpawnTimeForConsumerToBeStopped
func (k Keeper) AppendStopTimeForConsumerToBeStopped(ctx sdk.Context, consumerId string, stopTime time.Time) error {
	store := ctx.KVStore(k.storeKey)

	consumerIds, err := k.GetConsumersToBeStopped(ctx, stopTime)
	if err != nil {
		return err
	}
	consumerIds = append(consumerIds, consumerId)

	// sort so that we avoid getting a consumer id in front of everyone else and delying the removal of a chain
	sort.Slice(consumerIds, func(i, j int) bool {
		return consumerIds[i] < consumerIds[j]
	})

	var buf bytes.Buffer
	enc := gob.NewEncoder(&buf)
	err = enc.Encode(consumerIds)
	if err != nil {
		return err
	}

	store.Set(types.StopTimeToConsumerIdsKey(stopTime), buf.Bytes())
	return nil
}

// RemoveConsumerFromToBeStoppedConsumers
func (k Keeper) RemoveConsumerFromToBeStoppedConsumers(ctx sdk.Context, consumerId string, stopTime time.Time) error {
	store := ctx.KVStore(k.storeKey)

	consumerIds, err := k.GetConsumersToBeStopped(ctx, stopTime)
	if err != nil {
		return err
	}

	if len(consumerIds) == 0 {
		return fmt.Errorf("no consumer ids for stop time: %s", stopTime.String())
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
		return fmt.Errorf("failed to find consumer id (%s) in the chains to be stopped", consumerId)
	}

	if len(consumerIds) == 1 {
		store.Delete(types.StopTimeToConsumerIdsKey(stopTime))
		return nil
	}

	updatedConsumerIds := append(consumerIds[:index], consumerIds[index+1:]...)
	var buf bytes.Buffer
	enc := gob.NewEncoder(&buf)
	err = enc.Encode(updatedConsumerIds)
	if err != nil {
		return err
	}

	store.Set(types.StopTimeToConsumerIdsKey(stopTime), buf.Bytes())
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
		if len(result)+len(consumerIds) >= int(limit) {
			remainingConsumerIds := len(result) + len(consumerIds) - int(limit)
			if len(consumerIds[:len(consumerIds)-remainingConsumerIds]) == 0 {
				return result
			}
			return append(result, consumerIds[:len(consumerIds)-remainingConsumerIds]...)
		} else {
			result = append(result, consumerIds...)
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

// UpdateConsumer updates the chain with the provided consumer id
func (k Keeper) UpdateConsumer(ctx sdk.Context, consumerId string) error {
	phase, found := k.GetConsumerPhase(ctx, consumerId)
	if !found || phase == Stopped {
		return errorsmod.Wrapf(types.ErrInvalidPhase,
			"cannot update stopped or not existing chain: %s", consumerId)
	}

	updateRecord, err := k.GetConsumerUpdateRecord(ctx, consumerId)
	if err != nil {
		// TODO (permissionless) -- not really an invalid update record
		return errorsmod.Wrapf(types.ErrInvalidUpdateRecord,
			"did not find update record for chain: %s", consumerId)
	}

	k.DeleteAllowlist(ctx, consumerId)
	for _, address := range updateRecord.Allowlist {
		consAddr, err := sdk.ConsAddressFromBech32(address)
		if err != nil {
			continue
		}

		k.SetAllowlist(ctx, consumerId, types.NewProviderConsAddress(consAddr))
	}

	k.DeleteDenylist(ctx, consumerId)
	for _, address := range updateRecord.Denylist {
		consAddr, err := sdk.ConsAddressFromBech32(address)
		if err != nil {
			continue
		}

		k.SetDenylist(ctx, consumerId, types.NewProviderConsAddress(consAddr))
	}

	oldTopN := k.GetTopN(ctx, consumerId)
	if !found {
		oldTopN = 0
		k.Logger(ctx).Info("consumer chain top N not found, treating as 0", "consumerId", consumerId)
	}

	// if the top N changes, we need to update the new minimum power in top N
	if updateRecord.Top_N != oldTopN {
		if updateRecord.Top_N > 0 {
			// if the chain receives a non-zero top N value, store the minimum power in the top N
			bondedValidators, err := k.GetLastBondedValidators(ctx)
			if err != nil {
				return err
			}
			minPower, err := k.ComputeMinPowerInTopN(ctx, bondedValidators, updateRecord.Top_N)
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
		if len(result)+len(consumerIds) >= int(limit) {
			remainingConsumerIds := len(result) + len(consumerIds) - int(limit)
			if len(consumerIds[:len(consumerIds)-remainingConsumerIds]) == 0 {
				return result
			}
			return append(result, consumerIds[:len(consumerIds)-remainingConsumerIds]...)
		} else {
			result = append(result, consumerIds...)
		}

		consumerIds = append(consumerIds, string(iterator.Key()[1+8:]))
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
		record, err := k.GetConsumerRegistrationRecord(ctx, consumerId)
		if err != nil {
			k.Logger(ctx).Error("cannot find registration record",
				"consumerId", consumerId,
				"error", err)
			continue
		}

		if record.ChainId == chainId {
			return consumerId, true
		}

	}
	return "", false
}
