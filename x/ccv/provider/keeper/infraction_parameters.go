package keeper

import (
	"fmt"
	"time"

	storetypes "cosmossdk.io/store/types"
	sdk "github.com/cosmos/cosmos-sdk/types"

	"github.com/cosmos/interchain-security/v6/x/ccv/provider/types"
)

// GetInfractionParameters returns the slashing and jailing infraction parameters associated with this consumer id
func (k Keeper) GetInfractionParameters(ctx sdk.Context, consumerId string) (types.InfractionParameters, error) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerIdToInfractionParametersKey(consumerId))
	if bz == nil {
		return types.InfractionParameters{}, fmt.Errorf("failed to retrieve infraction parameters for consumer id (%s)", consumerId)
	}
	var infractionParameters types.InfractionParameters
	if err := infractionParameters.Unmarshal(bz); err != nil {
		return types.InfractionParameters{}, fmt.Errorf("failed to unmarshal infraction parameters for consumer id (%s): %w", consumerId, err)
	}

	return infractionParameters, nil
}

// SetInfractionParameters sets the slashing and jailing infraction parameters associated with this consumer id
func (k Keeper) SetInfractionParameters(ctx sdk.Context, consumerId string, parameters types.InfractionParameters) error {
	store := ctx.KVStore(k.storeKey)
	bz, err := parameters.Marshal()
	if err != nil {
		return fmt.Errorf("failed to marshal infraction parameters (%+v) for consumer id (%s): %w", parameters, consumerId, err)
	}

	store.Set(types.ConsumerIdToInfractionParametersKey(consumerId), bz)

	return nil
}

// DeleteInfractionParameters deletes the slashing and jailing infraction parameters associated with this consumer id
func (k Keeper) DeleteInfractionParameters(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerIdToInfractionParametersKey(consumerId))
}

// GetQueuedInfractionParameters returns the infraction parameters associated with this consumer id that are queued for future application
func (k Keeper) GetQueuedInfractionParameters(ctx sdk.Context, consumerId string) (types.InfractionParameters, error) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerIdToQueuedInfractionParametersKey(consumerId))
	if bz == nil {
		return types.InfractionParameters{}, fmt.Errorf("failed to retrieve queued infraction parameters for consumer id (%s)", consumerId)
	}

	var infractionParameters types.InfractionParameters
	if err := infractionParameters.Unmarshal(bz); err != nil {
		return types.InfractionParameters{}, fmt.Errorf("failed to unmarshal queued infraction parameters for consumer id (%s): %w", consumerId, err)
	}

	return infractionParameters, nil
}

// SetQueuedInfractionParameters sets the queued infraction parameters associated with this consumer id
func (k Keeper) SetQueuedInfractionParameters(ctx sdk.Context, consumerId string, parameters types.InfractionParameters) error {
	store := ctx.KVStore(k.storeKey)
	bz, err := parameters.Marshal()
	if err != nil {
		return fmt.Errorf("failed to marshal new infraction parameters (%+v) for consumer id (%s): %w", parameters, consumerId, err)
	}

	store.Set(types.ConsumerIdToQueuedInfractionParametersKey(consumerId), bz)

	return nil
}

// DeleteQueuedInfractionParameters deletes the queued infraction parameters associated with this consumer id
func (k Keeper) DeleteQueuedInfractionParameters(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerIdToQueuedInfractionParametersKey(consumerId))
}

// HasQueuedInfractionParameters checks if there is the queued infraction parameters associated with this consumer id
func (k Keeper) HasQueuedInfractionParameters(ctx sdk.Context, consumerId string) bool {
	store := ctx.KVStore(k.storeKey)
	return store.Has(types.ConsumerIdToQueuedInfractionParametersKey(consumerId))
}

// GetFromInfractionUpdateSchedule returns all the consumer ids of chains stored under this update time
func (k Keeper) GetFromInfractionUpdateSchedule(ctx sdk.Context, updateTime time.Time) (types.ConsumerIds, error) {
	return k.getConsumerIdsBasedOnTime(ctx, types.InfractionScheduledTimeToConsumerIdsKey, updateTime)
}

// AddToInfractionUpdateSchedule appends a consumer id to the timestamp-scheduled update list
func (k Keeper) AddToInfractionUpdateSchedule(ctx sdk.Context, consumerId string, updateTime time.Time) error {
	return k.appendConsumerIdOnTime(ctx, consumerId, types.InfractionScheduledTimeToConsumerIdsKey, updateTime)
}

// RemoveFromInfractionUpdateSchedule removes a consumer id from the timestamp-scheduled update list using specific timestamp
func (k Keeper) RemoveFromInfractionUpdateSchedule(ctx sdk.Context, consumerId string, updateTime time.Time) error {
	return k.removeConsumerIdFromTime(ctx, consumerId, types.InfractionScheduledTimeToConsumerIdsKey, updateTime)
}

// GetConsumerInfractionUpdateTime gets the time when the consumer's infraction parameters are scheduled for update
func (k Keeper) GetConsumerInfractionUpdateTime(ctx sdk.Context, consumerId string) (time.Time, error) {
	store := ctx.KVStore(k.storeKey)

	iterator := storetypes.KVStorePrefixIterator(store, []byte{types.InfractionScheduledTimeToConsumerIdsKeyPrefix()})
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		// parse the scheduled time from the key
		ts, err := types.ParseTime(types.InfractionScheduledTimeToConsumerIdsKeyPrefix(), iterator.Key())
		if err != nil {
			return time.Time{}, fmt.Errorf("failed to parse scheduled time: %w", err)
		}

		// get consumer ids associated with the scheduled time
		consumerIds, err := k.GetFromInfractionUpdateSchedule(ctx, ts)
		if err != nil {
			return time.Time{}, fmt.Errorf("failed to get record from time queue: %w", err)
		}

		// check if the target consumer id is in the list
		for _, id := range consumerIds.Ids {
			if id == consumerId {
				// remove the consumer id from the schedule and return
				if err := k.RemoveFromInfractionUpdateSchedule(ctx, consumerId, ts); err != nil {
					return time.Time{}, fmt.Errorf("failed to remove consumer id from time queue: %w", err)
				}
				return ts, nil
			}
		}
	}

	// consumer id was not found
	return time.Time{}, fmt.Errorf("consumer id %s not found in scheduled time queue", consumerId)
}

// DeleteAllConsumersFromInfractionUpdateSchedule deletes all consumer ids that should update infraction parameter at this specific update time
func (k Keeper) DeleteAllConsumersFromInfractionUpdateSchedule(ctx sdk.Context, updateTime time.Time) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.InfractionScheduledTimeToConsumerIdsKey(updateTime))
}

// RemoveConsumerInfractionQueuedData consumer intraction data from both queued parameters and time queue stores
func (k Keeper) RemoveConsumerInfractionQueuedData(ctx sdk.Context, consumerId string) {
	if k.HasQueuedInfractionParameters(ctx, consumerId) {
		// delete queued parameters
		k.DeleteQueuedInfractionParameters(ctx, consumerId)

		scheduledTime, err := k.GetConsumerInfractionUpdateTime(ctx, consumerId)
		if err != nil {
			return
		}
		// delete consumer id from time queue
		err = k.RemoveFromInfractionUpdateSchedule(ctx, consumerId, scheduledTime)
		if err != nil {
			return
		}
	}
}

// UpdateQueuedInfractionParams updates the infraction parameters in the time queue.
// Parameters for the specific consumer already exist in the queue:
//   - If the new parameters are the same as the current infraction parameters, the existing queued entry is removed to cancel the update.
//   - If the new parameters are different from both queued and current parameters, the existing entry is removed and new entry is added to the queue to schedule the update.
//
// Parameters for the specific consumer do not exist in the update queue and the new parameters differ from the consumer current infraction parameters,
// a new entry is added to the queue to schedule the update.
func (k Keeper) UpdateQueuedInfractionParams(ctx sdk.Context, consumerId string, newInfractionParams types.InfractionParameters) error {
	// remove the queued entry for this consumer ID if it exists
	k.RemoveConsumerInfractionQueuedData(ctx, consumerId)

	// get the current infraction parameters that must exist for the given consumer id
	currentInfractionParams, err := k.GetInfractionParameters(ctx, consumerId)
	if err != nil {
		return fmt.Errorf("failed to get current infraction parameters for consumer id (%s): %w", consumerId, err)
	}

	// if the new parameters are identical to the current parameters, cancel the update.
	// no action since any existing entry has already been removed above
	if compareInfractionParameters(currentInfractionParams, newInfractionParams) {
		return nil
	}

	// if the new parameters are different from the current queued parameters, queue the new infraction parameters to be applied after unbonding period
	err = k.SetQueuedInfractionParameters(ctx, consumerId, newInfractionParams)
	if err != nil {
		return err
	}

	// infraction parameters for this consumer will be updated once unbonding period elapses
	unbondingPeriod, err := k.stakingKeeper.UnbondingTime(ctx)
	if err != nil {
		return err
	}

	updateTime := ctx.BlockTime().Add(unbondingPeriod)
	err = k.AddToInfractionUpdateSchedule(ctx, consumerId, updateTime)
	if err != nil {
		return err
	}

	return nil
}

// BeginBlockUpdateInfractionParameters updates infraction parameters for consumer chain for which the update time has passed
func (k Keeper) BeginBlockUpdateInfractionParameters(ctx sdk.Context) error {
	consumerIds, err := k.ConsumeIdsFromTimeQueue(
		ctx,
		types.InfractionScheduledTimeToConsumerIdsKeyPrefix(),
		k.GetFromInfractionUpdateSchedule,
		k.DeleteAllConsumersFromInfractionUpdateSchedule,
		k.AddToInfractionUpdateSchedule,
		200,
	)
	if err != nil {
		return err
	}

	for _, consumerId := range consumerIds {
		// get queued consumer infraction parameters that needs to be applied
		queuedInfractionParams, err := k.GetQueuedInfractionParameters(ctx, consumerId)
		if err != nil {
			return err
		}

		// update consumer infraction parameters
		err = k.SetInfractionParameters(ctx, consumerId, queuedInfractionParams)
		if err != nil {
			return err
		}

		k.DeleteQueuedInfractionParameters(ctx, consumerId)
	}

	return nil
}

func compareInfractionParameters(param1, param2 types.InfractionParameters) bool {
	// Compare both DoubleSign and Downtime parameters
	return compareSlashJailParameters(param1.DoubleSign, param2.DoubleSign) &&
		compareSlashJailParameters(param1.Downtime, param2.Downtime)
}

func compareSlashJailParameters(param1, param2 *types.SlashJailParameters) bool {
	if param1 == nil && param2 == nil {
		return true
	}
	if param1 == nil || param2 == nil {
		return false
	}
	if param1.Tombstone != param2.Tombstone {
		return false
	}
	if !param1.SlashFraction.Equal(param2.SlashFraction) {
		return false
	}

	return param1.JailDuration == param2.JailDuration
}
