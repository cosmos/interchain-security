package keeper

import (
	errorsmod "cosmossdk.io/errors"
	storetypes "cosmossdk.io/store/types"
	"encoding/binary"
	"fmt"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	"time"
)

// ConsumerPhase captures the phases of a consumer chain according to `docs/docs/adrs/adr-018-permissionless-ics.md`
type ConsumerPhase byte

const (
	Registered ConsumerPhase = iota
	Initialized
	Launched
	Stopped
)

var DefaultUpdateRecord = types.ConsumerUpdateRecord{
	OwnerAddress:       "",
	Top_N:              0,
	ValidatorsPowerCap: 0,
	ValidatorSetCap:    0,
	Allowlist:          []string{},
	Denylist:           []string{},
}

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
func (k Keeper) FetchAndIncrementConsumerId(ctx sdk.Context) uint64 {
	consumerId, found := k.GetConsumerId(ctx)
	if !found {
		consumerId = 0
	}

	k.setConsumerId(ctx, consumerId+1)
	return consumerId
}

// GetConsumerIdToRegistrationRecord returns the registration record associated with this consumer id
func (k Keeper) GetConsumerIdToRegistrationRecord(ctx sdk.Context, consumerId string) (types.ConsumerRegistrationRecord, bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerIdToRegistrationRecordKey(consumerId))
	if bz == nil {
		return types.ConsumerRegistrationRecord{}, false
	}
	var record types.ConsumerRegistrationRecord
	if err := record.Unmarshal(bz); err != nil {
		panic(fmt.Errorf("failed to unmarshal record: %w", err))
	}
	return record, true
}

// SetConsumerIdToRegistrationRecord sets the registration record associated with this consumer id
func (k Keeper) SetConsumerIdToRegistrationRecord(ctx sdk.Context, consumerId string, record types.ConsumerRegistrationRecord) {
	store := ctx.KVStore(k.storeKey)
	bz, err := record.Marshal()
	if err != nil {
		panic(fmt.Errorf("failed to marshal record (%+v): %w", record, err))
	}
	store.Set(types.ConsumerIdToRegistrationRecordKey(consumerId), bz)
}

// DeleteConsumerIdToRegistrationRecord deletes the registration record associated with this consumer id
func (k Keeper) DeleteConsumerIdToRegistrationRecord(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerIdToRegistrationRecordKey(consumerId))
}

// GetConsumerIdToInitializationRecord returns the initialization record associated with this consumer id
func (k Keeper) GetConsumerIdToInitializationRecord(ctx sdk.Context, consumerId string) (types.ConsumerInitializationRecord, bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerIdToInitializationRecordKey(consumerId))
	if bz == nil {
		return types.ConsumerInitializationRecord{}, false
	}
	var record types.ConsumerInitializationRecord
	if err := record.Unmarshal(bz); err != nil {
		panic(fmt.Errorf("failed to unmarshal record: %w", err))
	}
	return record, true
}

// SetConsumerIdToInitializationRecord sets the initialization record associated with this consumer id
func (k Keeper) SetConsumerIdToInitializationRecord(ctx sdk.Context, consumerId string, record types.ConsumerInitializationRecord) {
	store := ctx.KVStore(k.storeKey)
	bz, err := record.Marshal()
	if err != nil {
		panic(fmt.Errorf("failed to marshal record (%+v): %w", record, err))
	}
	store.Set(types.ConsumerIdToInitializationRecordKey(consumerId), bz)
}

// DeleteConsumerIdToInitializationRecord deletes the initialization record associated with this consumer id
func (k Keeper) DeleteConsumerIdToInitializationRecord(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerIdToInitializationRecordKey(consumerId))
}

// GetConsumerIdToUpdateRecord returns the update record associated with this consumer id
func (k Keeper) GetConsumerIdToUpdateRecord(ctx sdk.Context, consumerId string) (types.ConsumerUpdateRecord, bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerIdToUpdateRecordKey(consumerId))
	if bz == nil {
		return types.ConsumerUpdateRecord{}, false
	}
	var record types.ConsumerUpdateRecord
	if err := record.Unmarshal(bz); err != nil {
		panic(fmt.Errorf("failed to unmarshal record: %w", err))
	}
	return record, true
}

// GetConsumerIdToUpdateRecordOrDefault returns the update record associated with this consumer id or the default record
// if there is no update record associated with this consumer id
func (k Keeper) GetConsumerIdToUpdateRecordOrDefault(ctx sdk.Context, consumerId string, defaultRecord types.ConsumerUpdateRecord) types.ConsumerUpdateRecord {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerIdToUpdateRecordKey(consumerId))
	if bz == nil {
		return defaultRecord
	}
	var record types.ConsumerUpdateRecord
	if err := record.Unmarshal(bz); err != nil {
		panic(fmt.Errorf("failed to unmarshal record: %w", err))
	}
	return record
}

// SetConsumerIdToUpdateRecord sets the update record associated with this consumer id
func (k Keeper) SetConsumerIdToUpdateRecord(ctx sdk.Context, consumerId string, record types.ConsumerUpdateRecord) {
	store := ctx.KVStore(k.storeKey)
	bz, err := record.Marshal()
	if err != nil {
		panic(fmt.Errorf("failed to marshal record (%+v): %w", record, err))
	}
	store.Set(types.ConsumerIdToUpdateRecordKey(consumerId), bz)
}

// DeleteConsumerIdToUpdateRecord deletes the update record associated with this consumer id
func (k Keeper) DeleteConsumerIdToUpdateRecord(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerIdToUpdateRecordKey(consumerId))
}

// GetConsumerIdToOwnerAddress returns the owner address associated with this consumer id
func (k Keeper) GetConsumerIdToOwnerAddress(ctx sdk.Context, consumerId string) (string, bool) {
	store := ctx.KVStore(k.storeKey)
	buf := store.Get(types.ConsumerIdToOwnerAddressKey(consumerId))
	if buf == nil {
		return "", false
	}
	return string(buf), true
}

// SetConsumerIdToOwnerAddress sets the owner address associated with this consumer id
func (k Keeper) SetConsumerIdToOwnerAddress(ctx sdk.Context, consumerId string, ownerAddress string) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.ConsumerIdToOwnerAddressKey(consumerId), []byte(ownerAddress))
}

// DeleteConsumerIdToOwnerAddress deletes the owner address associated with this consumer id
func (k Keeper) DeleteConsumerIdToOwnerAddress(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerIdToOwnerAddressKey(consumerId))
}

// GetConsumerIdToPhase returns the phase associated with this consumer id
func (k Keeper) GetConsumerIdToPhase(ctx sdk.Context, consumerId string) (ConsumerPhase, bool) {
	store := ctx.KVStore(k.storeKey)
	buf := store.Get(types.ConsumerIdToPhaseKey(consumerId))
	if buf == nil {
		return ConsumerPhase(0), false
	}
	return ConsumerPhase(buf[0]), true
}

// SetConsumerIdToPhase sets the phase associated with this consumer id
// TODO (PERMISSIONLESS): use this method when launching and when stopping a chain
func (k Keeper) SetConsumerIdToPhase(ctx sdk.Context, consumerId string, phase ConsumerPhase) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.ConsumerIdToPhaseKey(consumerId), []byte{byte(phase)})
}

// DeleteConsumerIdToPhase deletes the phase associated with this consumer id
func (k Keeper) DeleteConsumerIdToPhase(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerIdToPhaseKey(consumerId))
}

// GetConsumerIdToStopTime returns the stop time associated with the to-be-stopped chain with consumer id
func (k Keeper) GetConsumerIdToStopTime(ctx sdk.Context, consumerId string) (time.Time, bool) {
	store := ctx.KVStore(k.storeKey)
	buf := store.Get(types.ConsumerIdToStopTimeKey(consumerId))
	if buf == nil {
		return time.Time{}, false
	}
	var time time.Time
	if err := time.UnmarshalBinary(buf); err != nil {
		panic(fmt.Errorf("failed to unmarshal time: %w", err))
	}
	return time, true
}

// SetConsumerIdToStopTime sets the stop time associated with this consumer id
func (k Keeper) SetConsumerIdToStopTime(ctx sdk.Context, consumerId string, stopTime time.Time) {
	store := ctx.KVStore(k.storeKey)
	buf, err := stopTime.MarshalBinary()
	if err != nil {
		panic(fmt.Errorf("failed to marshal time: %w", err))
	}
	store.Set(types.ConsumerIdToStopTimeKey(consumerId), buf)
}

// DeleteConsumerIdToStopTime deletes the stop time associated with this consumer id
func (k Keeper) DeleteConsumerIdToStopTime(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerIdToStopTimeKey(consumerId))
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
func (k Keeper) GetInitializedConsumersReadyToLaunch(ctx sdk.Context) []string {
	store := ctx.KVStore(k.storeKey)
	iterator := storetypes.KVStorePrefixIterator(store, types.ConsumerIdToInitializationRecordKeyPrefix())
	defer iterator.Close()

	var consumerIds []string

	for ; iterator.Valid(); iterator.Next() {
		// the `consumerId` resides in the whole key, but we skip the first byte (because it's the `ConsumerIdKey`)
		// plus 8 more bytes for the `uint64` in the key that contains the length of the `consumerId`
		consumerId := string(iterator.Key()[1+8:])

		var record types.ConsumerInitializationRecord
		err := record.Unmarshal(iterator.Value())
		if err != nil {
			panic(fmt.Errorf("failed to unmarshal consumer record: %w for consumer id: %s", err, consumerId))
		}

		// if current block time is equal to or after spawnTime, and the chain is initialized, we can launch the chain
		phase, found := k.GetConsumerIdToPhase(ctx, consumerId)
		if !ctx.BlockTime().Before(record.SpawnTime) && (found && phase == Initialized) {
			consumerIds = append(consumerIds, consumerId)
		}
	}

	return consumerIds
}

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

func (k Keeper) UpdateConsumer(ctx sdk.Context, consumerId string) error {
	phase, found := k.GetConsumerIdToPhase(ctx, consumerId)
	if !found || phase == Stopped {
		return errorsmod.Wrapf(types.ErrInvalidPhase,
			"cannot update stopped or not existing chain: %s", consumerId)
	}

	updateRecord, found := k.GetConsumerIdToUpdateRecord(ctx, consumerId)
	if !found {
		// TODO (permissionless) -- not really an invalid update record
		return errorsmod.Wrapf(types.ErrInvalidUpdateRecord,
			"did not find update record for chain: %s", consumerId)
	}

	k.SetTopN(ctx, consumerId, updateRecord.Top_N)
	k.SetValidatorsPowerCap(ctx, consumerId, updateRecord.ValidatorsPowerCap)
	k.SetValidatorSetCap(ctx, consumerId, updateRecord.ValidatorSetCap)

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

	oldTopN, found := k.GetTopN(ctx, consumerId)
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

	k.SetMinStake(ctx, consumerId, updateRecord.MinStake)
	k.SetInactiveValidatorsAllowed(ctx, consumerId, updateRecord.AllowInactiveVals)

	return nil
}

// GetLaunchedConsumersReadyToStop returns the consumer ids of the pending launched consumer chains
// that are ready to stop
func (k Keeper) GetLaunchedConsumersReadyToStop(ctx sdk.Context) []string {
	store := ctx.KVStore(k.storeKey)
	iterator := storetypes.KVStorePrefixIterator(store, types.ConsumerIdToStopTimeKeyNamePrefix())
	defer iterator.Close()

	var consumerIds []string

	for ; iterator.Valid(); iterator.Next() {
		// the `consumerId` resides in the whole key, but we skip the first byte (because it's the `ConsumerIdKey`)
		// plus 8 more bytes for the `uint64` in the key that contains the length of the `consumerId`
		consumerId := string(iterator.Key()[1+8:])

		var stopTime time.Time
		err := stopTime.UnmarshalBinary(iterator.Value())
		if err != nil {
			panic(fmt.Errorf("failed to unmarshal stop stopTime: %w for consumer id: %s", err, consumerId))
		}

		// if current block time is equal to or after stop stopTime, and the chain is launched we can stop the chain
		phase, found := k.GetConsumerIdToPhase(ctx, consumerId)
		if !ctx.BlockTime().Before(stopTime) && (found && phase == Launched) {
			consumerIds = append(consumerIds, string(iterator.Key()[1+8:]))
		}
	}

	return consumerIds
}

// IsValidatorOptedInToChain checks if the validator with `providerAddr` is opted into the chain with the specified `chainId`.
// It returns `found == true` and the corresponding chain's `consumerId` if the validator is opted in. Otherwise, it returns an empty string
// for `consumerId` and `found == false`.
func (k Keeper) IsValidatorOptedInToChain(ctx sdk.Context, providerAddr types.ProviderConsAddress, chainId string) (consumerId string, found bool) {
	store := ctx.KVStore(k.storeKey)
	iterator := storetypes.KVStorePrefixIterator(store, types.ConsumerIdToRegistrationRecordKeyPrefix())
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		// the `currentConsumerId` resides in the whole key, but we skip the first byte (because it's the `ConsumerIdKey`)
		// plus 8 more bytes for the `uint64` in the key that contains the length of the `currentConsumerId`
		currentConsumerId := string(iterator.Key()[1+8:])

		var record types.ConsumerRegistrationRecord
		err := record.Unmarshal(iterator.Value())
		if err != nil {
			panic(fmt.Errorf("failed to unmarshal registration record: %w for consumer id: %s", err, currentConsumerId))
		}

		if record.ChainId == chainId && k.IsOptedIn(ctx, currentConsumerId, providerAddr) {
			return currentConsumerId, true
		}
	}
	return "", false
}