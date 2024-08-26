package v8

import (
	"bytes"
	"encoding/binary"
	"fmt"
	"time"

	errorsmod "cosmossdk.io/errors"
	storetypes "cosmossdk.io/store/types"
	sdk "github.com/cosmos/cosmos-sdk/types"

	providerkeeper "github.com/cosmos/interchain-security/v5/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/v5/x/ccv/types"
)

const (
	LegacyUnbondingOpBytePrefix                = byte(11)
	LegacyConsumerAddrsToPruneBytePrefix       = byte(25)
	LegacyMaturedUnbondingOpsByteKey           = byte(1)
	LegacyUnbondingOpIndexBytePrefix           = byte(12)
	LegacyInitTimeoutTimestampBytePrefix       = byte(8)
	LegacyVscSendTimestampBytePrefix           = byte(18)
	LegacyVSCMaturedHandledThisBlockBytePrefix = byte(28)

	LegacyPendingCAPKeyPrefix            = byte(9)
	LegacyPendingCRPKeyPrefix            = byte(10)
	LegacyProposedConsumerChainKeyPrefix = byte(30)

	LegacyThrottledPacketDataSizeKeyPrefix = byte(19)
	LegacyThrottledPacketDataKeyPrefix     = byte(20)
	LegacyGlobalSlashEntryKeyPrefix        = byte(21)
	LegacyTopNKeyPrefix                    = byte(33)
	LegacyValidatorsPowerCapKeyPrefix      = byte(34)
	LegacyValidatorSetCapKeyPrefix         = byte(35)

	LegacyChainToChannelKeyPrefix = byte(5)
	LegacyChannelToChainKeyPrefix = byte(6)
	LegacyChainToClientKeyPrefix  = byte(7)

	// needed for rekeying
	ConsumerGenesisKeyPrefix               = byte(14)
	SlashAcksKeyPrefix                     = byte(15)
	InitChainHeightKeyPrefix               = byte(16)
	PendingVSCsKeyPrefix                   = byte(17)
	EquivocationEvidenceMinHeightKeyPrefix = byte(29)
	MinimumPowerInTopNKeyPrefix            = byte(40)
)

// CompleteUnbondingOps completes all unbonding operations.
// Note that it must be executed before CleanupState.
func CompleteUnbondingOps(ctx sdk.Context, store storetypes.KVStore, pk providerkeeper.Keeper) {
	iterator := storetypes.KVStorePrefixIterator(store, []byte{LegacyUnbondingOpBytePrefix})
	defer func() {
		if err := iterator.Close(); err != nil {
			pk.Logger(ctx).Error("Failed to close iterator", "error", err)
		}
	}()

	for ; iterator.Valid(); iterator.Next() {
		id := binary.BigEndian.Uint64(iterator.Key()[1:])
		if err := pk.UnbondingCanComplete(ctx, id); err != nil {
			pk.Logger(ctx).Error("UnbondingCanComplete failed", "unbondingID", id, "error", err.Error())
		}
	}
}

// MigrateConsumerAddrsToPrune migrates the ConsumerAddrsToPrune index to ConsumerAddrsToPruneV2.
// Note: This migration must be done before removing the VscSendTimestamp index
func MigrateConsumerAddrsToPrune(ctx sdk.Context, store storetypes.KVStore, pk providerkeeper.Keeper) error {
	iterator := storetypes.KVStorePrefixIterator(store, []byte{LegacyConsumerAddrsToPruneBytePrefix})
	defer iterator.Close()

	unbondingPeriod, err := pk.UnbondingTime(ctx)
	if err != nil {
		return err
	}

	for ; iterator.Valid(); iterator.Next() {
		chainID, vscID, err := providertypes.ParseStringIdAndUintIdKey(LegacyConsumerAddrsToPruneBytePrefix, iterator.Key())
		if err != nil {
			pk.Logger(ctx).Error("ParseChainIdAndUintIdKey failed while migrating ConsumerAddrsToPrune",
				"key", string(iterator.Key()),
				"error", err.Error(),
			)
			continue
		}
		// use the VscSendTimestamp index to compute the timestamp after which this consumer address can be pruned
		vscSendTimestampKey := providertypes.StringIdAndUintIdKey(LegacyVscSendTimestampBytePrefix, chainID, vscID)
		var sentTime time.Time
		if timeBz := store.Get(vscSendTimestampKey); timeBz != nil {
			if ts, err := sdk.ParseTimeBytes(timeBz); err == nil {
				sentTime = ts
			} else {
				pk.Logger(ctx).Error("MigrateConsumerAddrsToPrune failed parsing VSC send timestamp key", "error", err.Error())
				continue
			}
		} else {
			pk.Logger(ctx).Error(
				"MigrateConsumerAddrsToPrune cannot find VSC send timestamp",
				"chainID", chainID,
				"vscID", vscID,
			)
			continue
		}
		pruneAfterTs := sentTime.Add(unbondingPeriod).UTC()

		var addrs providertypes.AddressList
		err = addrs.Unmarshal(iterator.Value())
		if err != nil {
			pk.Logger(ctx).Error("MigrateConsumerAddrsToPrune failed unmarshaling data from store", "key", string(iterator.Value()))
			continue
		}

		for _, addr := range addrs.Addresses {
			consumerAddr := providertypes.NewConsumerConsAddress(addr)
			pk.AppendConsumerAddrsToPrune(ctx, chainID, pruneAfterTs, consumerAddr)
		}
	}

	return nil
}

// MigrateLaunchedConsumerChains migrates all the state for consumer chains with an existing client
// Note that it must be executed before CleanupState.
func MigrateLaunchedConsumerChains(ctx sdk.Context, store storetypes.KVStore, pk providerkeeper.Keeper) error {
	chainIds := []string{}
	iterator := storetypes.KVStorePrefixIterator(store, []byte{LegacyChainToClientKeyPrefix})
	for ; iterator.Valid(); iterator.Next() {
		// remove 1 byte prefix from key to retrieve chainID
		chainId := string(iterator.Key()[1:])
		chainIds = append(chainIds, chainId)
	}
	err := iterator.Close()
	if err != nil {
		return err
	}

	for _, chainId := range chainIds {
		// create new consumerID
		consumerId := pk.FetchAndIncrementConsumerId(ctx)

		// re-key store

		// chainId -> clientId
		rekeyFromChainIdToConsumerId(store, LegacyChainToClientKeyPrefix, chainId, consumerId)
		// chainId -> channelId
		rekeyFromChainIdToConsumerId(store, LegacyChainToChannelKeyPrefix, chainId, consumerId)
		// chainId -> consumer genesis
		rekeyFromChainIdToConsumerId(store, ConsumerGenesisKeyPrefix, chainId, consumerId)
		// chainId -> SlashAcks
		rekeyFromChainIdToConsumerId(store, SlashAcksKeyPrefix, chainId, consumerId)
		// chainId -> InitChainHeight
		rekeyFromChainIdToConsumerId(store, InitChainHeightKeyPrefix, chainId, consumerId)
		// chainId -> PendingVSCs
		rekeyFromChainIdToConsumerId(store, PendingVSCsKeyPrefix, chainId, consumerId)
		// chainId -> EquivocationEvidenceMinHeight
		rekeyFromChainIdToConsumerId(store, EquivocationEvidenceMinHeightKeyPrefix, chainId, consumerId)
		// chainId -> MinimumPowerInTopN
		rekeyFromChainIdToConsumerId(store, MinimumPowerInTopNKeyPrefix, chainId, consumerId)

		// chainId -> ConsumerValidators
		rekeyChainIdAndConsAddrKey(store, providertypes.ConsumerValidatorsKeyPrefix(), chainId, consumerId)
		// chainId -> ValidatorsByConsumerAddr
		rekeyChainIdAndConsAddrKey(store, providertypes.ValidatorsByConsumerAddrKeyPrefix(), chainId, consumerId)
		// chainId -> ConsumerCommissionRate
		rekeyChainIdAndConsAddrKey(store, providertypes.ConsumerCommissionRateKeyPrefix(), chainId, consumerId)
		// chainId -> ConsumerValidator
		rekeyChainIdAndConsAddrKey(store, providertypes.ConsumerValidatorKeyPrefix(), chainId, consumerId)
		// chainId -> Allowlist
		rekeyChainIdAndConsAddrKey(store, providertypes.AllowlistKeyPrefix(), chainId, consumerId)
		// chainId -> Denylist
		rekeyChainIdAndConsAddrKey(store, providertypes.DenylistKeyPrefix(), chainId, consumerId)
		// chainId -> OptedIn
		rekeyChainIdAndConsAddrKey(store, providertypes.OptedInKeyPrefix(), chainId, consumerId)

		// chainId -> ConsumerAddrsToPruneV2
		rekeyChainIdAndTsKey(store, providertypes.ConsumerAddrsToPruneV2KeyPrefix(), chainId, consumerId)

		// set channelId -> consumerId mapping
		channelId, found := pk.GetConsumerIdToChannelId(ctx, consumerId)
		if !found {
			return errorsmod.Wrapf(ccv.ErrInvalidConsumerState, "cannot find channel ID associated with consumer ID: %s", consumerId)
		}
		pk.SetChannelToConsumerId(ctx, channelId, consumerId)

		// set clientId -> consumerId mapping
		clinetId, found := pk.GetConsumerClientId(ctx, consumerId)
		if !found {
			return errorsmod.Wrapf(ccv.ErrInvalidConsumerState, "cannot find client ID associated with consumer ID: %s", consumerId)
		}
		pk.SetClientIdToConsumerId(ctx, clinetId, consumerId)

		// set ownership -- all existing chains are owned by gov
		pk.SetConsumerOwnerAddress(ctx, consumerId, pk.GetAuthority())
		pk.SetConsumerChainId(ctx, consumerId, chainId)

		// set phase to launched
		// TODO make sure the chain cannot be in Stopped phase
		pk.SetConsumerPhase(ctx, consumerId, providerkeeper.Launched)

		// Note: ConsumerMetadata will be populated in the upgrade handler

		// Note: InitializationParameters is not needed since the chain is already launched

		// migrate power shaping params
		topNKey := append([]byte{LegacyTopNKeyPrefix}, []byte(chainId)...)
		var topN uint32 = 0
		buf := store.Get(topNKey)
		if buf != nil {
			topN = binary.BigEndian.Uint32(buf)
		}
		validatorsPowerCapKey := append([]byte{LegacyValidatorsPowerCapKeyPrefix}, []byte(chainId)...)
		var validatorsPowerCap uint32 = 0
		buf = store.Get(validatorsPowerCapKey)
		if buf != nil {
			validatorsPowerCap = binary.BigEndian.Uint32(buf)
		}
		validatorSetCapKey := append([]byte{LegacyValidatorSetCapKeyPrefix}, []byte(chainId)...)
		var validatorSetCap uint32 = 0
		buf = store.Get(validatorSetCapKey)
		if buf != nil {
			validatorSetCap = binary.BigEndian.Uint32(buf)
		}
		powerShapingParameters := providertypes.PowerShapingParameters{
			Top_N:              topN,
			ValidatorsPowerCap: validatorsPowerCap,
			ValidatorSetCap:    validatorSetCap,
			Allowlist:          []string{}, // leave empty
			Denylist:           []string{}, // leave empty
			MinStake:           0,
			AllowInactiveVals:  false,
		}
		err := pk.SetConsumerPowerShapingParameters(ctx, consumerId, powerShapingParameters)
		if err != nil {
			return err
		}

		// TODO other keys
		// - ConsumerIdToStopTimeKey
		// - ProviderConsAddrToOptedInConsumerIdsKey
		// - ...

	}

	return nil
}

// MigratePreLaunchedConsumerChains migrates all the state for consumer chains not yet launched
// Note that it must be executed before CleanupState.
func MigratePreLaunchedConsumerChains(ctx sdk.Context, store storetypes.KVStore, pk providerkeeper.Keeper) error {
	props, err := legacyGetAllPendingConsumerAdditionProps(store)
	if err != nil {
		return err
	}

	for _, prop := range props {
		// TODO
		// - each prop should have a spawn time set, so it can be added to AppendConsumerToBeLaunchedOnSpawnTime
		// - populate the state accordingly, including the InitializationParameters
	}

	// Note that the keys are deleted in CleanupState

	return nil
}

// MigrateStoppedConsumerChains migrates all the state for consumer chains about to be stopped
// Note that it must be executed before CleanupState.
func MigrateStoppedConsumerChains(ctx sdk.Context, store storetypes.KVStore, pk providerkeeper.Keeper) error {
	props, err := legacyGetAllPendingConsumerRemovalProps(store)
	if err != nil {
		return err
	}

	for _, prop := range props {
		// TODO
		// - each prop should have a stop time set, so it can be added to AppendConsumerToBeStoppedOnStopTime
		// - populate the state accordingly
	}

	// Note that the keys are deleted in CleanupState

	return nil
}

// rekeyFromChainIdToConsumerId migrates store keys from `keyPrefix | chainId`
// to  `keyPrefix | consumerId` leaving the value unchanged
func rekeyFromChainIdToConsumerId(
	store storetypes.KVStore,
	keyPrefix byte,
	chainId, consumerId string,
) {
	oldKey := append([]byte{keyPrefix}, []byte(chainId)...)
	value := store.Get(oldKey)
	newKey := append([]byte{keyPrefix}, []byte(consumerId)...)
	store.Set(newKey, value)
	store.Delete(oldKey)
}

// rekeyChainIdAndConsAddrKey migrates store keys
// from `keyPrefix | len(chainID) | chainID | ConsAddress`
// to `keyPrefix | len(consumerId) | consumerId | ConsAddress“
// leaving the value unchanged
func rekeyChainIdAndConsAddrKey(
	store storetypes.KVStore,
	keyPrefix byte,
	chainId, consumerId string,
) error {
	oldPartialKey := providertypes.StringIdWithLenKey(keyPrefix, chainId)
	addrs := []sdk.ConsAddress{}
	iterator := storetypes.KVStorePrefixIterator(store, oldPartialKey)
	for ; iterator.Valid(); iterator.Next() {
		_, addr, err := providertypes.ParseStringIdAndConsAddrKey(keyPrefix, iterator.Key())
		if err != nil {
			return err
		}
		addrs = append(addrs, addr)
	}
	err := iterator.Close()
	if err != nil {
		return err
	}

	for _, addr := range addrs {
		oldKey := providertypes.StringIdAndConsAddrKey(keyPrefix, chainId, addr)
		value := store.Get(oldKey)
		newKey := providertypes.StringIdAndConsAddrKey(keyPrefix, consumerId, addr)
		store.Set(newKey, value)
		store.Delete(oldKey)
	}

	return nil
}

// rekeyChainIdAndTsKey migrates store keys
// from `keyPrefix | len(chainID) | chainID | timestamp`
// to `keyPrefix | len(consumerId) | consumerId | timestamp
// leaving the value unchanged
func rekeyChainIdAndTsKey(
	store storetypes.KVStore,
	keyPrefix byte,
	chainId, consumerId string,
) error {
	oldPartialKey := providertypes.StringIdWithLenKey(keyPrefix, chainId)
	timestamps := []time.Time{}
	iterator := storetypes.KVStorePrefixIterator(store, oldPartialKey)
	for ; iterator.Valid(); iterator.Next() {
		_, ts, err := providertypes.ParseStringIdAndTsKey(keyPrefix, iterator.Key())
		if err != nil {
			return err
		}
		timestamps = append(timestamps, ts)
	}
	err := iterator.Close()
	if err != nil {
		return err
	}

	for _, ts := range timestamps {
		oldKey := providertypes.StringIdAndTsKey(keyPrefix, chainId, ts)
		value := store.Get(oldKey)
		newKey := providertypes.StringIdAndTsKey(keyPrefix, consumerId, ts)
		store.Set(newKey, value)
		store.Delete(oldKey)
	}

	return nil
}

// CleanupState removes deprecated state
func CleanupState(store storetypes.KVStore) {
	removePrefix(store, LegacyMaturedUnbondingOpsByteKey)
	removePrefix(store, LegacyUnbondingOpBytePrefix)
	removePrefix(store, LegacyUnbondingOpIndexBytePrefix)
	removePrefix(store, LegacyInitTimeoutTimestampBytePrefix)
	removePrefix(store, LegacyVscSendTimestampBytePrefix)
	removePrefix(store, LegacyVSCMaturedHandledThisBlockBytePrefix)
	removePrefix(store, LegacyConsumerAddrsToPruneBytePrefix)

	removePrefix(store, LegacyPendingCAPKeyPrefix)
	removePrefix(store, LegacyPendingCRPKeyPrefix)
	removePrefix(store, LegacyProposedConsumerChainKeyPrefix)

	removePrefix(store, LegacyThrottledPacketDataSizeKeyPrefix)
	removePrefix(store, LegacyThrottledPacketDataKeyPrefix)
	removePrefix(store, LegacyGlobalSlashEntryKeyPrefix)

	removePrefix(store, LegacyTopNKeyPrefix)
	removePrefix(store, LegacyValidatorsPowerCapKeyPrefix)
	removePrefix(store, LegacyValidatorSetCapKeyPrefix)
}

func removePrefix(store storetypes.KVStore, prefix byte) {
	iterator := storetypes.KVStorePrefixIterator(store, []byte{prefix})
	defer iterator.Close()

	var keysToDel [][]byte
	for ; iterator.Valid(); iterator.Next() {
		keysToDel = append(keysToDel, iterator.Key())
	}
	for _, delKey := range keysToDel {
		store.Delete(delKey)
	}
}

// legacyGetAllPendingConsumerAdditionProps gets all pending consumer addition proposals.
//
// Note that the pending consumer addition proposals are stored under keys with the following format:
// PendingCAPKeyPrefix | spawnTime.UnixNano() | consumerId
// Thus, the returned array is in spawnTime order. If two proposals have the same spawnTime,
// then they are ordered by consumerId.
func legacyGetAllPendingConsumerAdditionProps(store storetypes.KVStore) ([]providertypes.ConsumerAdditionProposal, error) {
	props := []providertypes.ConsumerAdditionProposal{}
	iterator := storetypes.KVStorePrefixIterator(store, []byte{LegacyPendingCAPKeyPrefix})
	for ; iterator.Valid(); iterator.Next() {
		var prop providertypes.ConsumerAdditionProposal
		err := prop.Unmarshal(iterator.Value())
		if err != nil {
			return props, err
		}
		props = append(props, prop)
	}
	err := iterator.Close()
	if err != nil {
		return props, err
	}
	return props, nil
}

func legacyGetAllPendingConsumerRemovalProps(store storetypes.KVStore) ([]providertypes.ConsumerRemovalProposal, error) {
	props := []providertypes.ConsumerRemovalProposal{}
	iterator := storetypes.KVStorePrefixIterator(store, []byte{LegacyPendingCRPKeyPrefix})
	for ; iterator.Valid(); iterator.Next() {
		var prop providertypes.ConsumerRemovalProposal
		err := prop.Unmarshal(iterator.Value())
		if err != nil {
			return props, err
		}
		props = append(props, prop)
	}
	err := iterator.Close()
	if err != nil {
		return props, err
	}
	return props, nil
}

// legacyGetAllProposedConsumerChainIDs returns the proposed consumer ids of all gov proposals that are still in the voting period
func legacyGetAllProposedConsumerChainIDs(store storetypes.KVStore) ([]providertypes.ProposedChain, error) {
	proposedChains := []providertypes.ProposedChain{}
	iterator := storetypes.KVStorePrefixIterator(store, []byte{LegacyProposedConsumerChainKeyPrefix})
	for ; iterator.Valid(); iterator.Next() {
		proposalID, err := legacyParseProposedConsumerChainKey(iterator.Key())
		if err != nil {
			return proposedChains, err
		}
		proposedChains = append(proposedChains, providertypes.ProposedChain{
			ConsumerId: string(iterator.Value()),
			ProposalID: proposalID,
		})

	}
	err := iterator.Close()
	if err != nil {
		return proposedChains, err
	}

	return proposedChains, nil
}

// ParseProposedConsumerChainKey get the proposalID in the key
func legacyParseProposedConsumerChainKey(bz []byte) (uint64, error) {
	expectedPrefix := []byte{LegacyProposedConsumerChainKeyPrefix}
	prefixL := len(expectedPrefix)
	if prefix := bz[:prefixL]; !bytes.Equal(prefix, expectedPrefix) {
		return 0, fmt.Errorf("invalid prefix; expected: %X, got: %X", expectedPrefix, prefix)
	}
	proposalID := sdk.BigEndianToUint64(bz[prefixL:])

	return proposalID, nil
}
