package keeper

import (
	"encoding/binary"
	"fmt"
	"strconv"
	"time"

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
