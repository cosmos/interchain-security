package keeper

import (
	"fmt"
	"time"

	tmtypes "github.com/cometbft/cometbft/types"

	errorsmod "cosmossdk.io/errors"
	storetypes "cosmossdk.io/store/types"

	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v8/modules/core/04-channel/types"
	commitmenttypes "github.com/cosmos/ibc-go/v8/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v8/modules/light-clients/07-tendermint"

	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/v5/x/ccv/types"
)

// BeginBlockLaunchConsumers launches initialized consumers that are ready to launch
func (k Keeper) BeginBlockLaunchConsumers(ctx sdk.Context) {
	// TODO (PERMISSIONLESS): we can parameterize the limit
	for _, consumerId := range k.GetConsumersReadyToLaunch(ctx, 200) {
		record, err := k.GetConsumerInitializationParameters(ctx, consumerId)
		if err != nil {
			ctx.Logger().Error("could not retrieve initialization record",
				"consumerId", consumerId,
				"error", err)
			continue
		}
		// Remove consumer to prevent re-trying launching this chain.
		// We would only try to re-launch this chain if a new `MsgUpdateConsumer` message is sent.
		err = k.RemoveConsumerToBeLaunched(ctx, consumerId, record.SpawnTime)
		if err != nil {
			ctx.Logger().Error("could not remove consumer from to-be-launched queue",
				"consumerId", consumerId,
				"error", err)
			continue
		}

		cachedCtx, writeFn := ctx.CacheContext()
		err = k.LaunchConsumer(cachedCtx, consumerId)
		if err != nil {
			ctx.Logger().Error("could not launch chain",
				"consumerId", consumerId,
				"error", err)
			continue
		}
		k.SetConsumerPhase(cachedCtx, consumerId, types.ConsumerPhase_CONSUMER_PHASE_LAUNCHED)

		// the cached context is created with a new EventManager, so we merge the events into the original context
		ctx.EventManager().EmitEvents(cachedCtx.EventManager().Events())
		writeFn()
	}
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

// CreateConsumerClient will create the CCV client for the given consumer chain. The CCV channel must be built
// on top of the CCV client to ensure connection with the right consumer chain.
func (k Keeper) CreateConsumerClient(ctx sdk.Context, consumerId string) error {
	initializationRecord, err := k.GetConsumerInitializationParameters(ctx, consumerId)
	if err != nil {
		return err
	}

	phase := k.GetConsumerPhase(ctx, consumerId)
	if phase != types.ConsumerPhase_CONSUMER_PHASE_INITIALIZED {
		return errorsmod.Wrapf(types.ErrInvalidPhase,
			"cannot create client for consumer chain that is not in the Initialized phase but in phase %d: %s", phase, consumerId)
	}

	chainId, err := k.GetConsumerChainId(ctx, consumerId)
	if err != nil {
		return err
	}

	// Set minimum height for equivocation evidence from this consumer chain
	k.SetEquivocationEvidenceMinHeight(ctx, consumerId, initializationRecord.InitialHeight.RevisionHeight)

	// Consumers start out with the unbonding period from the consumer addition prop
	consumerUnbondingPeriod := initializationRecord.UnbondingPeriod

	// Create client state by getting template client from parameters and filling in zeroed fields from proposal.
	clientState := k.GetTemplateClient(ctx)
	clientState.ChainId = chainId
	clientState.LatestHeight = initializationRecord.InitialHeight

	trustPeriod, err := ccv.CalculateTrustPeriod(consumerUnbondingPeriod, k.GetTrustingPeriodFraction(ctx))
	if err != nil {
		return err
	}
	clientState.TrustingPeriod = trustPeriod
	clientState.UnbondingPeriod = consumerUnbondingPeriod

	consumerGen, validatorSetHash, err := k.MakeConsumerGenesis(ctx, consumerId)
	if err != nil {
		return err
	}
	err = k.SetConsumerGenesis(ctx, consumerId, consumerGen)
	if err != nil {
		return err
	}

	// Create consensus state
	consensusState := ibctmtypes.NewConsensusState(
		ctx.BlockTime(),
		commitmenttypes.NewMerkleRoot([]byte(ibctmtypes.SentinelRoot)),
		validatorSetHash, // use the hash of the updated initial valset
	)

	clientID, err := k.clientKeeper.CreateClient(ctx, clientState, consensusState)
	if err != nil {
		return err
	}
	k.SetConsumerClientId(ctx, consumerId, clientID)

	k.Logger(ctx).Info("consumer chain launched (client created)",
		"consumer id", consumerId,
		"client id", clientID,
	)

	ctx.EventManager().EmitEvent(
		sdk.NewEvent(
			types.EventTypeConsumerClientCreated,
			sdk.NewAttribute(sdk.AttributeKeyModule, types.ModuleName),
			sdk.NewAttribute(ccv.AttributeChainID, consumerId),
			sdk.NewAttribute(clienttypes.AttributeKeyClientID, clientID),
			sdk.NewAttribute(types.AttributeInitialHeight, initializationRecord.InitialHeight.String()),
			sdk.NewAttribute(types.AttributeTrustingPeriod, clientState.TrustingPeriod.String()),
			sdk.NewAttribute(types.AttributeUnbondingPeriod, clientState.UnbondingPeriod.String()),
		),
	)

	return nil
}

// MakeConsumerGenesis returns the created consumer genesis state for consumer chain `consumerId`,
// as well as the validator hash of the initial validator set of the consumer chain
func (k Keeper) MakeConsumerGenesis(
	ctx sdk.Context,
	consumerId string,
) (gen ccv.ConsumerGenesisState, nextValidatorsHash []byte, err error) {
	initializationRecord, err := k.GetConsumerInitializationParameters(ctx, consumerId)
	if err != nil {
		return gen, nil, errorsmod.Wrapf(ccv.ErrInvalidConsumerState,
			"cannot retrieve initialization parameters: %s", err.Error())
	}
	powerShapingParameters, err := k.GetConsumerPowerShapingParameters(ctx, consumerId)
	if err != nil {
		return gen, nil, errorsmod.Wrapf(ccv.ErrInvalidConsumerState,
			"cannot retrieve power shaping parameters: %s", err.Error())
	}

	providerUnbondingPeriod, err := k.stakingKeeper.UnbondingTime(ctx)
	if err != nil {
		return gen, nil, errorsmod.Wrapf(types.ErrNoUnbondingTime, "unbonding time not found: %s", err)
	}
	height := clienttypes.GetSelfHeight(ctx)

	clientState := k.GetTemplateClient(ctx)
	// this is the counter party chain ID for the consumer
	clientState.ChainId = ctx.ChainID()
	// this is the latest height the client was updated at, i.e.,
	// the height of the latest consensus state (see below)
	clientState.LatestHeight = height
	trustPeriod, err := ccv.CalculateTrustPeriod(providerUnbondingPeriod, k.GetTrustingPeriodFraction(ctx))
	if err != nil {
		return gen, nil, errorsmod.Wrapf(sdkerrors.ErrInvalidHeight, "error %s calculating trusting_period for: %s", err, height)
	}
	clientState.TrustingPeriod = trustPeriod
	clientState.UnbondingPeriod = providerUnbondingPeriod

	consState, err := k.clientKeeper.GetSelfConsensusState(ctx, height)
	if err != nil {
		return gen, nil, errorsmod.Wrapf(clienttypes.ErrConsensusStateNotFound, "error %s getting self consensus state for: %s", err, height)
	}

	// get the bonded validators from the staking module
	bondedValidators, err := k.GetLastBondedValidators(ctx)
	if err != nil {
		return gen, nil, errorsmod.Wrapf(stakingtypes.ErrNoValidatorFound, "error getting last bonded validators: %s", err)
	}

	minPower := int64(0)
	if powerShapingParameters.Top_N > 0 {
		// get the consensus active validators
		// we do not want to base the power calculation for the top N
		// on inactive validators, too, since the top N will be a percentage of the active set power
		// otherwise, it could be that inactive validators are forced to validate
		activeValidators, err := k.GetLastProviderConsensusActiveValidators(ctx)
		if err != nil {
			return gen, nil, errorsmod.Wrapf(stakingtypes.ErrNoValidatorFound, "error getting last active bonded validators: %s", err)
		}

		// in a Top-N chain, we automatically opt in all validators that belong to the top N
		minPower, err = k.ComputeMinPowerInTopN(ctx, activeValidators, powerShapingParameters.Top_N)
		if err != nil {
			return gen, nil, err
		}
		// log the minimum power in top N
		k.Logger(ctx).Info("minimum power in top N at consumer genesis",
			"consumerId", consumerId,
			"minPower", minPower,
		)
		k.OptInTopNValidators(ctx, consumerId, activeValidators, minPower)
		k.SetMinimumPowerInTopN(ctx, consumerId, minPower)
	}

	// need to use the bondedValidators, not activeValidators, here since the chain might be opt-in and allow inactive vals
	nextValidators := k.ComputeNextValidators(ctx, consumerId, bondedValidators, powerShapingParameters, minPower)
	k.SetConsumerValSet(ctx, consumerId, nextValidators)

	// get the initial updates with the latest set consumer public keys
	initialUpdatesWithConsumerKeys := DiffValidators([]types.ConsensusValidator{}, nextValidators)

	// Get a hash of the consumer validator set from the update with applied consumer assigned keys
	updatesAsValSet, err := tmtypes.PB2TM.ValidatorUpdates(initialUpdatesWithConsumerKeys)
	if err != nil {
		return gen, nil, fmt.Errorf("unable to create validator set from updates computed from key assignment in MakeConsumerGenesis: %s", err)
	}
	hash := tmtypes.NewValidatorSet(updatesAsValSet).Hash()

	consumerGenesisParams := ccv.NewParams(
		true,
		initializationRecord.BlocksPerDistributionTransmission,
		initializationRecord.DistributionTransmissionChannel,
		"", // providerFeePoolAddrStr,
		initializationRecord.CcvTimeoutPeriod,
		initializationRecord.TransferTimeoutPeriod,
		initializationRecord.ConsumerRedistributionFraction,
		initializationRecord.HistoricalEntries,
		initializationRecord.UnbondingPeriod,
		[]string{},
		[]string{},
		ccv.DefaultRetryDelayPeriod,
	)

	gen = *ccv.NewInitialConsumerGenesisState(
		clientState,
		consState.(*ibctmtypes.ConsensusState),
		initialUpdatesWithConsumerKeys,
		consumerGenesisParams,
	)
	return gen, hash, nil
}

// BeginBlockStopConsumers iterates over the pending consumer proposals and stop/removes the chain if the stop time has passed
func (k Keeper) BeginBlockStopConsumers(ctx sdk.Context) {
	// TODO (PERMISSIONLESS): parameterize the limit
	for _, consumerId := range k.GetConsumersReadyToStop(ctx, 200) {
		// stop consumer chain in a cached context to handle errors
		cachedCtx, writeFn := ctx.CacheContext()

		stopTime, err := k.GetConsumerStopTime(ctx, consumerId)
		if err != nil {
			k.Logger(ctx).Error("chain could not be stopped",
				"consumerId", consumerId,
				"err", err.Error())
			continue
		}

		err = k.StopConsumerChain(cachedCtx, consumerId, true)
		if err != nil {
			k.Logger(ctx).Error("consumer chain could not be stopped",
				"consumerId", consumerId,
				"err", err.Error())
			continue
		}

		k.SetConsumerPhase(cachedCtx, consumerId, types.ConsumerPhase_CONSUMER_PHASE_STOPPED)

		err = k.RemoveConsumerToBeStopped(ctx, consumerId, stopTime)
		if err != nil {
			ctx.Logger().Error("could not remove consumer from to-be-stopped queue",
				"consumerId", consumerId,
				"error", err)
			continue
		}

		// The cached context is created with a new EventManager so we merge the event into the original context
		ctx.EventManager().EmitEvents(cachedCtx.EventManager().Events())

		writeFn()

		k.Logger(ctx).Info("executed consumer removal",
			"consumer id", consumerId,
			"stop time", stopTime,
		)
	}
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

// StopConsumerChain cleans up the states for the given consumer id
func (k Keeper) StopConsumerChain(ctx sdk.Context, consumerId string, closeChan bool) (err error) {
	// check that a client for consumerId exists
	// TODO (PERMISSIONLESS): change to use phases instead
	if _, found := k.GetConsumerClientId(ctx, consumerId); !found {
		return errorsmod.Wrap(types.ErrConsumerChainNotFound,
			fmt.Sprintf("cannot stop non-existent consumer chain: %s", consumerId))
	}

	// clean up states
	k.DeleteConsumerClientId(ctx, consumerId)
	k.DeleteConsumerGenesis(ctx, consumerId)
	// Note: this call panics if the key assignment state is invalid
	k.DeleteKeyAssignments(ctx, consumerId)
	k.DeleteMinimumPowerInTopN(ctx, consumerId)
	k.DeleteEquivocationEvidenceMinHeight(ctx, consumerId)

	// close channel and delete the mappings between chain ID and channel ID
	if channelID, found := k.GetConsumerIdToChannelId(ctx, consumerId); found {
		if closeChan {
			// Close the channel for the given channel ID on the condition
			// that the channel exists and isn't already in the CLOSED state
			channel, found := k.channelKeeper.GetChannel(ctx, ccv.ProviderPortID, channelID)
			if found && channel.State != channeltypes.CLOSED {
				err := k.chanCloseInit(ctx, channelID)
				if err != nil {
					k.Logger(ctx).Error("channel to consumer chain could not be closed",
						"consumerId", consumerId,
						"channelID", channelID,
						"error", err.Error(),
					)
				}
			}
		}
		k.DeleteConsumerIdToChannelId(ctx, consumerId)
		k.DeleteChannelIdToConsumerId(ctx, channelID)
	}

	// delete consumer commission rate
	provAddrs := k.GetAllCommissionRateValidators(ctx, consumerId)
	for _, addr := range provAddrs {
		k.DeleteConsumerCommissionRate(ctx, consumerId, addr)
	}

	k.DeleteInitChainHeight(ctx, consumerId)
	k.DeleteSlashAcks(ctx, consumerId)
	k.DeletePendingVSCPackets(ctx, consumerId)

	k.DeleteConsumerMetadata(ctx, consumerId)
	k.DeleteConsumerPowerShapingParameters(ctx, consumerId)
	k.DeleteConsumerPowerShapingParameters(ctx, consumerId)
	k.DeleteAllowlist(ctx, consumerId)
	k.DeleteDenylist(ctx, consumerId)
	k.DeleteAllOptedIn(ctx, consumerId)
	k.DeleteConsumerValSet(ctx, consumerId)

	// TODO (PERMISSIONLESS) add newly-added state to be deleted

	k.Logger(ctx).Info("consumer chain removed from provider", "consumerId", consumerId)

	return nil
}

//
// Setters and Getters
//

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