package v8

import (
	"encoding/binary"
	"time"

	"github.com/cosmos/cosmos-sdk/types/bech32"

	errorsmod "cosmossdk.io/errors"
	storetypes "cosmossdk.io/store/types"
	sdk "github.com/cosmos/cosmos-sdk/types"

	providerkeeper "github.com/cosmos/interchain-security/v6/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/v6/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/v6/x/ccv/types"
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
	ConsumerRewardsAllocationKeyPrefix     = byte(38)
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

func TransformConsAddressesToBech32Addresses(addresses []providertypes.ProviderConsAddress) []string {
	bech32PrefixConsAddr := sdk.GetConfig().GetBech32ConsensusAddrPrefix()
	var bech32Addresses []string
	for _, addr := range addresses {
		bech32Addr, _ := bech32.ConvertAndEncode(bech32PrefixConsAddr, addr.ToSdkConsAddr().Bytes())
		bech32Addresses = append(bech32Addresses, bech32Addr)
	}
	return bech32Addresses
}

// MigrateLaunchedConsumerChains migrates all the state for consumer chains with an existing client
// Note that it must be executed before CleanupState.
func MigrateLaunchedConsumerChains(ctx sdk.Context, store storetypes.KVStore, pk providerkeeper.Keeper) error {
	chainIds := []string{}
	iterator := storetypes.KVStorePrefixIterator(store, []byte{LegacyChainToClientKeyPrefix})
	for ; iterator.Valid(); iterator.Next() {
		// remove 1 byte prefix from key to retrieve chainId
		chainId := string(iterator.Key()[1:])
		chainIds = append(chainIds, chainId)
	}
	err := iterator.Close()
	if err != nil {
		return err
	}

	for _, chainId := range chainIds {
		// create new consumerId
		consumerId := pk.FetchAndIncrementConsumerId(ctx)

		// re-key store

		// channelId -> chainId
		channelId, found := pk.GetConsumerIdToChannelId(ctx, chainId)
		if !found {
			return errorsmod.Wrapf(ccv.ErrInvalidConsumerState, "cannot find channel id associated with consumer id: %s", consumerId)
		}
		pk.SetChannelToConsumerId(ctx, channelId, consumerId)

		// chainId -> channelId
		rekeyFromChainIdToConsumerId(store, LegacyChainToChannelKeyPrefix, chainId, consumerId)

		// chainId -> clientId
		rekeyFromChainIdToConsumerId(store, LegacyChainToClientKeyPrefix, chainId, consumerId)

		// chainId -> consumer genesis
		rekeyFromChainIdToConsumerId(store, ConsumerGenesisKeyPrefix, chainId, consumerId)

		// chainId -> SlashAcks
		rekeyFromChainIdToConsumerId(store, SlashAcksKeyPrefix, chainId, consumerId)

		// chainId -> InitChainHeight
		rekeyFromChainIdToConsumerId(store, InitChainHeightKeyPrefix, chainId, consumerId)

		// chainId -> PendingVSCs
		rekeyFromChainIdToConsumerId(store, PendingVSCsKeyPrefix, chainId, consumerId)

		// chainId -> ConsumerValidators
		err := rekeyChainIdAndConsAddrKey(store, providertypes.ConsumerValidatorsKeyPrefix(), chainId, consumerId)
		if err != nil {
			return err
		}

		// chainId -> ValidatorsByConsumerAddr
		err = rekeyChainIdAndConsAddrKey(store, providertypes.ValidatorsByConsumerAddrKeyPrefix(), chainId, consumerId)
		if err != nil {
			return err
		}

		// chainId -> EquivocationEvidenceMinHeight
		rekeyFromChainIdToConsumerId(store, EquivocationEvidenceMinHeightKeyPrefix, chainId, consumerId)

		// chainId -> ConsumerValidator
		err = rekeyChainIdAndConsAddrKey(store, providertypes.ConsumerValidatorKeyPrefix(), chainId, consumerId)
		if err != nil {
			return err
		}

		// chainId -> OptedIn
		err = rekeyChainIdAndConsAddrKey(store, providertypes.OptedInKeyPrefix(), chainId, consumerId)
		if err != nil {
			return err
		}

		// chainId -> Allowlist
		err = rekeyChainIdAndConsAddrKey(store, providertypes.AllowlistKeyPrefix(), chainId, consumerId)
		if err != nil {
			return err
		}

		// chainId -> Denylist
		err = rekeyChainIdAndConsAddrKey(store, providertypes.DenylistKeyPrefix(), chainId, consumerId)
		if err != nil {
			return err
		}

		// chainId -> ConsumerRewardsAllocations
		rekeyFromChainIdToConsumerId(store, ConsumerRewardsAllocationKeyPrefix, chainId, consumerId)

		// chainId -> ConsumerCommissionRate
		err = rekeyChainIdAndConsAddrKey(store, providertypes.ConsumerCommissionRateKeyPrefix(), chainId, consumerId)
		if err != nil {
			return err
		}

		// chainId -> MinimumPowerInTopN
		oldKey := providertypes.StringIdWithLenKey(MinimumPowerInTopNKeyPrefix, chainId)
		value := store.Get(oldKey)
		if value != nil {
			newKey := providertypes.StringIdWithLenKey(MinimumPowerInTopNKeyPrefix, consumerId)
			store.Set(newKey, value)
			store.Delete(oldKey)
		}

		// chainId -> ConsumerAddrsToPruneV2
		err = rekeyChainIdAndTsKey(store, providertypes.ConsumerAddrsToPruneV2KeyPrefix(), chainId, consumerId)
		if err != nil {
			return err
		}

		pk.SetConsumerChainId(ctx, consumerId, chainId)

		// set ownership -- all existing chains are owned by gov
		pk.SetConsumerOwnerAddress(ctx, consumerId, pk.GetAuthority())

		// Note: ConsumerMetadata will be populated in the upgrade handler
		// Note: InitializationParameters is not needed since the chain is already launched

		// migrate power shaping params
		topNKey := providertypes.StringIdWithLenKey(LegacyTopNKeyPrefix, chainId)
		var topN uint32 = 0
		buf := store.Get(topNKey)
		if buf != nil {
			topN = binary.BigEndian.Uint32(buf)
		}

		validatorsPowerCapKey := providertypes.StringIdWithLenKey(LegacyValidatorsPowerCapKeyPrefix, chainId)
		var validatorsPowerCap uint32 = 0
		buf = store.Get(validatorsPowerCapKey)
		if buf != nil {
			validatorsPowerCap = binary.BigEndian.Uint32(buf)
		}

		validatorSetCapKey := providertypes.StringIdWithLenKey(LegacyValidatorSetCapKeyPrefix, chainId)
		var validatorSetCap uint32 = 0
		buf = store.Get(validatorSetCapKey)
		if buf != nil {
			validatorSetCap = binary.BigEndian.Uint32(buf)
		}

		allowlist := TransformConsAddressesToBech32Addresses(pk.GetAllowList(ctx, consumerId))
		denylist := TransformConsAddressesToBech32Addresses(pk.GetDenyList(ctx, consumerId))

		powerShapingParameters := providertypes.PowerShapingParameters{
			Top_N:              topN,
			ValidatorsPowerCap: validatorsPowerCap,
			ValidatorSetCap:    validatorSetCap,
			Allowlist:          allowlist,
			Denylist:           denylist,
			// do not set those since they do not exist in a previous interchain-security version and hence cannot be set
			MinStake:          0,
			AllowInactiveVals: false,
		}
		err = pk.SetConsumerPowerShapingParameters(ctx, consumerId, powerShapingParameters)
		if err != nil {
			return err
		}

		// set phase to launched
		pk.SetConsumerPhase(ctx, consumerId, providertypes.CONSUMER_PHASE_LAUNCHED)

		// This is to migrate everything under `ProviderConsAddrToOptedInConsumerIdsKey`
		// `OptedIn` was already re-keyed earlier (see above) and hence we can use `consumerId` here.
		for _, providerConsAddr := range pk.GetAllOptedIn(ctx, consumerId) {
			err := pk.AppendOptedInConsumerId(ctx, providerConsAddr, consumerId)
			if err != nil {
				return err
			}
		}

		// set clientId -> consumerId mapping
		// consumer to client was already re-keyed so we can use `consumerId` here
		// however, during the rekeying, the reverse index was not set
		clientId, found := pk.GetConsumerClientId(ctx, consumerId)
		if !found {
			return errorsmod.Wrapf(ccv.ErrInvalidConsumerState, "cannot find client ID associated with consumer ID: %s", consumerId)
		}
		pk.SetConsumerClientId(ctx, consumerId, clientId)
	}

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
	if value != nil {
		newKey := append([]byte{keyPrefix}, []byte(consumerId)...)
		store.Set(newKey, value)
		store.Delete(oldKey)
	}
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
		if value == nil {
			// this should not happen, but just in case as Set will fail if value is nil
			continue
		}
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
		if value == nil {
			// this should not happen, but just in case as Set will fail if value is nil
			continue
		}
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
