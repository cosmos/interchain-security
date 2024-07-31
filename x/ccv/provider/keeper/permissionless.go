package keeper

import (
	storetypes "cosmossdk.io/store/types"
	"encoding/binary"
	"fmt"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
)

// ConsumerPhase captures the phases of a consumer chain according to `docs/docs/adrs/adr-018-permissionless-ics.md`
type ConsumerPhase byte

const (
	Registered ConsumerPhase = iota
	Initialized
	Launched
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
func (k Keeper) FetchAndIncrementConsumerId(ctx sdk.Context) uint64 {
	consumerId, found := k.GetConsumerId(ctx)
	if !found {
		consumerId = 0
	}

	k.setConsumerId(ctx, consumerId+1)
	return consumerId
}

// GetConsumerIdToChainId returns the chain id associated with this consumer id
func (k Keeper) GetConsumerIdToChainId(ctx sdk.Context, consumerId string) (string, bool) {
	store := ctx.KVStore(k.storeKey)
	buf := store.Get(types.ConsumerIdToChainIdKey(consumerId))
	if buf == nil {
		return "", false
	}
	return string(buf), true
}

// SetConsumerIdToChainId sets the chain id associated with this consumer id
func (k Keeper) SetConsumerIdToChainId(ctx sdk.Context, consumerId string, chainId string) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.ConsumerIdToChainIdKey(consumerId), []byte(chainId))
}

// DeleteConsumerIdToChainId deletes the chain id to consumer id association
func (k Keeper) DeleteConsumerIdToChainId(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerIdToChainIdKey(consumerId))
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

// DeleteConsumerIdToInitializationRecord deletes the initializatoin record associated with this consumer id
func (k Keeper) DeleteConsumerIdToInitializationRecord(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerIdToInitializationRecordKey(consumerId))
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
// TODO (PERMISSIONLESS): use this method when launching and when stopping a chian
func (k Keeper) SetConsumerIdToPhase(ctx sdk.Context, consumerId string, phase ConsumerPhase) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.ConsumerIdToPhaseKey(consumerId), []byte{byte(phase)})
}

// DeleteConsumerIdToPhase deletes the phase associated with this consumer id
func (k Keeper) DeleteConsumerIdToPhase(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerIdToPhaseKey(consumerId))
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
	iterator := storetypes.KVStorePrefixIterator(store, types.ConsumerIdToInitializationRecordKeyNameKeyPrefix())
	defer iterator.Close()

	var consumerIds []string

	for ; iterator.Valid(); iterator.Next() {
		var record types.ConsumerInitializationRecord
		err := record.Unmarshal(iterator.Value())
		if err != nil {
			panic(fmt.Errorf("failed to unmarshal consumer record: %w for consumer id: %s", err, string(iterator.Value())))
		}

		if !ctx.BlockTime().Before(record.SpawnTime) {
			// the `consumerId` resides in the whole key, but we skip the first byte (because it's the `ConsumerIdKey`)
			// plus 8 more bytes for the `uint64` in the key that contains the length of the `consumerId`
			consumerIds = append(consumerIds, string(iterator.Key()[1+8:]))
		}
	}

	return consumerIds
}
