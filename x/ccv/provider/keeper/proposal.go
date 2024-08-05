package keeper

import (
	"fmt"
	"time"

	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v8/modules/core/04-channel/types"
	commitmenttypes "github.com/cosmos/ibc-go/v8/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v8/modules/light-clients/07-tendermint"

	errorsmod "cosmossdk.io/errors"
	storetypes "cosmossdk.io/store/types"

	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"

	tmtypes "github.com/cometbft/cometbft/types"

	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/v5/x/ccv/types"
)

// Wrapper for the new proposal message MsgChangeRewardDenoms
// Will replace legacy handler HandleLegacyConsumerRewardDenomProposal
func (k Keeper) HandleConsumerRewardDenomProposal(ctx sdk.Context, proposal *types.MsgChangeRewardDenoms) error {
	p := types.ChangeRewardDenomsProposal{
		DenomsToAdd:    proposal.DenomsToAdd,
		DenomsToRemove: proposal.DenomsToRemove,
	}

	return k.HandleLegacyConsumerRewardDenomProposal(ctx, &p)
}

// CreateConsumerClient will create the CCV client for the given consumer chain. The CCV channel must be built
// on top of the CCV client to ensure connection with the right consumer chain.
func (k Keeper) CreateConsumerClient(ctx sdk.Context, consumerId string) error {
	initializationRecord, found := k.GetConsumerIdToInitializationRecord(ctx, consumerId)
	if !found {
		return errorsmod.Wrapf(types.ErrNoInitializationRecord,
			"initialization record for consumer chain: %s is missing", consumerId)
	}

	phase, found := k.GetConsumerIdToPhase(ctx, consumerId)
	if !found || phase != Initialized {
		return errorsmod.Wrapf(types.ErrInvalidPhase,
			"cannot create client for consumer chain that is neither in the initialized phase: %s", consumerId)
	}

	// TODO (PERMISSIONLESS): make this a function ... GetChainId(consumerId) ...
	registrationRecord, found := k.GetConsumerIdToRegistrationRecord(ctx, consumerId)
	if !found {
		return errorsmod.Wrapf(types.ErrNoChainId,
			"the chain id for this consumer chain: %s is missing", consumerId)
	}
	chainId := registrationRecord.ChainId

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

	k.Logger(ctx).Info("consumer chain registered (client created)",
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

	k.DeleteTopN(ctx, consumerId)
	k.DeleteValidatorsPowerCap(ctx, consumerId)
	k.DeleteValidatorSetCap(ctx, consumerId)
	k.DeleteAllowlist(ctx, consumerId)
	k.DeleteDenylist(ctx, consumerId)
	k.DeleteMinStake(ctx, consumerId)
	k.DisableInactiveValidators(ctx, consumerId)

	k.DeleteAllOptedIn(ctx, consumerId)
	k.DeleteConsumerValSet(ctx, consumerId)

	// TODO (PERMISSIONLESS) add newly-added state to be deleted

	k.Logger(ctx).Info("consumer chain removed from provider", "consumerId", consumerId)

	return nil
}

// MakeConsumerGenesis returns the created consumer genesis state for consumer chain `consumerId`,
// as well as the validator hash of the initial validator set of the consumer chain
func (k Keeper) MakeConsumerGenesis(
	ctx sdk.Context,
	consumerId string,
) (gen ccv.ConsumerGenesisState, nextValidatorsHash []byte, err error) {
	initializationRecord, found := k.GetConsumerIdToInitializationRecord(ctx, consumerId)
	if !found {
		return gen, nil, errorsmod.Wrapf(types.ErrNoInitializationRecord,
			"initialization record for consumer chain: %s is missing", consumerId)

	}
	updateRecord := k.GetConsumerIdToUpdateRecordOrDefault(ctx, consumerId, DefaultUpdateRecord)

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

	if updateRecord.Top_N > 0 {
		// get the consensus active validators
		// we do not want to base the power calculation for the top N
		// on inactive validators, too, since the top N will be a percentage of the active set power
		// otherwise, it could be that inactive validators are forced to validate
		activeValidators, err := k.GetLastProviderConsensusActiveValidators(ctx)
		if err != nil {
			return gen, nil, errorsmod.Wrapf(stakingtypes.ErrNoValidatorFound, "error getting last active bonded validators: %s", err)
		}
		// in a Top-N chain, we automatically opt in all validators that belong to the top N
		minPower, err := k.ComputeMinPowerInTopN(ctx, activeValidators, updateRecord.Top_N)
		if err != nil {
			return gen, nil, err
		}
		k.OptInTopNValidators(ctx, consumerId, activeValidators, minPower)
		k.SetMinimumPowerInTopN(ctx, consumerId, minPower)
	}
	// need to use the bondedValidators, not activeValidators, here since the chain might be opt-in and allow inactive vals
	nextValidators := k.ComputeNextValidators(ctx, consumerId, bondedValidators)
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

// SetPendingConsumerAdditionProp stores a pending consumer addition proposal.
//
// Note that the pending consumer addition proposals are stored under keys with
// the following format: PendingCAPKeyPrefix | spawnTime | chainID
// Thus, if multiple consumer addition proposal for the same chain will pass at
// the same time, then only the last one will be stored.
func (k Keeper) SetPendingConsumerAdditionProp(ctx sdk.Context, prop *types.ConsumerAdditionProposal) {
	store := ctx.KVStore(k.storeKey)
	bz, err := prop.Marshal()
	if err != nil {
		// An error here would indicate something is very wrong
		panic(fmt.Errorf("failed to marshal consumer addition proposal: %w", err))
	}
	store.Set(types.PendingCAPKey(prop.SpawnTime, prop.ChainId), bz)
}

// GetPendingConsumerAdditionProp retrieves a pending consumer addition proposal
// by spawn time and chain id.
//
// Note: this method is only used in testing
func (k Keeper) GetPendingConsumerAdditionProp(ctx sdk.Context, spawnTime time.Time,
	chainID string,
) (prop types.ConsumerAdditionProposal, found bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.PendingCAPKey(spawnTime, chainID))
	if bz == nil {
		return prop, false
	}
	err := prop.Unmarshal(bz)
	if err != nil {
		// An error here would indicate something is very wrong,
		// the ConsumerAdditionProp is assumed to be correctly serialized in SetPendingConsumerAdditionProp.
		panic(fmt.Errorf("failed to unmarshal consumer addition proposal: %w", err))
	}

	return prop, true
}

// BeginBlockInit iterates over the initialized consumers chains and creates clients for chains
// in which the spawn time has passed
func (k Keeper) BeginBlockInit(ctx sdk.Context) {
	for _, consumerId := range k.GetInitializedConsumersReadyToLaunch(ctx) {
		cachedCtx, writeFn := ctx.CacheContext()
		err := k.LaunchConsumer(cachedCtx, consumerId)
		if err != nil {
			ctx.Logger().Error("could not launch chain",
				"consumerId", consumerId,
				"error", err)
			continue
		}
		k.SetConsumerIdToPhase(cachedCtx, consumerId, Launched)
		writeFn()
	}
}

// GetConsumerAdditionPropsToExecute returns the pending consumer addition proposals
// that are ready to be executed, i.e., consumer clients to be created.
// A prop is included in the returned list if its proposed spawn time has passed.
//
// Note: this method is split out from BeginBlockInit to be easily unit tested.
func (k Keeper) GetConsumerAdditionPropsToExecute(ctx sdk.Context) (propsToExecute []types.ConsumerAdditionProposal) {
	store := ctx.KVStore(k.storeKey)
	iterator := storetypes.KVStorePrefixIterator(store, types.PendingCAPKeyPrefix())

	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		var prop types.ConsumerAdditionProposal
		err := prop.Unmarshal(iterator.Value())
		if err != nil {
			// An error here would indicate something is very wrong,
			// the ConsumerAdditionProp is assumed to be correctly serialized in SetPendingConsumerAdditionProp.
			panic(fmt.Errorf("failed to unmarshal consumer addition proposal: %w", err))
		}

		if !ctx.BlockTime().Before(prop.SpawnTime) {
			propsToExecute = append(propsToExecute, prop)
		} else {
			break
		}
	}

	return propsToExecute
}

// GetAllPendingConsumerAdditionProps gets all pending consumer addition proposals.
//
// Note that the pending consumer addition proposals are stored under keys with the following format:
// PendingCAPKeyPrefix | spawnTime.UnixNano() | chainID
// Thus, the returned array is in spawnTime order. If two proposals have the same spawnTime,
// then they are ordered by chainID.
func (k Keeper) GetAllPendingConsumerAdditionProps(ctx sdk.Context) (props []types.ConsumerAdditionProposal) {
	store := ctx.KVStore(k.storeKey)
	iterator := storetypes.KVStorePrefixIterator(store, types.PendingCAPKeyPrefix())

	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		var prop types.ConsumerAdditionProposal
		err := prop.Unmarshal(iterator.Value())
		if err != nil {
			// An error here would indicate something is very wrong,
			// the ConsumerAdditionProp is assumed to be correctly serialized in SetPendingConsumerAdditionProp.
			panic(fmt.Errorf("failed to unmarshal consumer addition proposal: %w", err))
		}

		props = append(props, prop)
	}

	return props
}

// DeletePendingConsumerAdditionProps deletes the given consumer addition proposals
func (k Keeper) DeletePendingConsumerAdditionProps(ctx sdk.Context, proposals ...types.ConsumerAdditionProposal) {
	store := ctx.KVStore(k.storeKey)

	for _, p := range proposals {
		store.Delete(types.PendingCAPKey(p.SpawnTime, p.ChainId))
	}
}

// SetPendingConsumerRemovalProp stores a pending consumer removal proposal.
//
// Note that the pending removal addition proposals are stored under keys with
// the following format: PendingCRPKeyPrefix | stopTime | chainID
// Thus, if multiple removal addition proposal for the same chain will pass at
// the same time, then only the last one will be stored.
func (k Keeper) SetPendingConsumerRemovalProp(ctx sdk.Context, prop *types.ConsumerRemovalProposal) {
	store := ctx.KVStore(k.storeKey)
	bz, err := prop.Marshal()
	if err != nil {
		// An error here would indicate something is very wrong
		panic(fmt.Errorf("failed to marshal consumer removal proposal: %w", err))
	}
	store.Set(types.PendingCRPKey(prop.StopTime, prop.ConsumerId), bz)
}

// PendingConsumerRemovalPropExists checks whether a pending consumer removal proposal
// exists for the given consumer chain ID and stopTime
//
// Note: this method is only used in testing
func (k Keeper) PendingConsumerRemovalPropExists(ctx sdk.Context, chainID string, timestamp time.Time) bool {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.PendingCRPKey(timestamp, chainID))

	return bz != nil
}

// DeletePendingConsumerRemovalProps deletes the given pending consumer removal proposals.
// This method should be called once the proposal has been acted upon.
func (k Keeper) DeletePendingConsumerRemovalProps(ctx sdk.Context, proposals ...types.ConsumerRemovalProposal) {
	store := ctx.KVStore(k.storeKey)

	for _, p := range proposals {
		store.Delete(types.PendingCRPKey(p.StopTime, p.ConsumerId))
	}
}

// BeginBlockCCR iterates over the pending consumer proposals and stop/removes the chain if the stop time has passed
func (k Keeper) BeginBlockCCR(ctx sdk.Context) {
	for _, consumerId := range k.GetLaunchedConsumersReadyToStop(ctx) {
		// stop consumer chain in a cached context to handle errors
		cachedCtx, writeFn := ctx.CacheContext()

		stopTime, found := k.GetConsumerIdToStopTime(ctx, consumerId)
		if !found {
			ctx.Logger().Info("this chain (%s) is not meant to be stopped", consumerId)
			continue
		}

		err := k.StopConsumerChain(cachedCtx, consumerId, true)
		if err != nil {
			ctx.Logger().Info("consumer chain could not be stopped: %w", err)
			continue
		}
		// The cached context is created with a new EventManager so we merge the event
		// into the original context
		// TODO (PERMISSIONLESS): verify this here and in the initialized chains to launch
		ctx.EventManager().EmitEvents(cachedCtx.EventManager().Events())

		k.SetConsumerIdToPhase(cachedCtx, consumerId, Stopped)
		writeFn()

		k.Logger(ctx).Info("executed consumer removal",
			"consumer id", consumerId,
			"stop time", stopTime,
		)
	}
}

//// GetConsumerRemovalPropsToExecute iterates over the pending consumer removal proposals
//// and returns an ordered list of consumer removal proposals to be executed,
//// ie. consumer chains to be stopped and removed from the provider chain.
//// A prop is included in the returned list if its proposed stop time has passed.
////
//// Note: this method is split out from BeginBlockCCR to be easily unit tested.
//func (k Keeper) GetConsumerRemovalPropsToExecute(ctx sdk.Context) []types.ConsumerRemovalProposal {
//	// store the (to be) executed consumer removal proposals in order
//	propsToExecute := []types.ConsumerRemovalProposal{}
//
//	store := ctx.KVStore(k.storeKey)
//	iterator := storetypes.KVStorePrefixIterator(store, types.PendingCRPKeyPrefix())
//	defer iterator.Close()
//
//	for ; iterator.Valid(); iterator.Next() {
//		var prop types.ConsumerRemovalProposal
//		err := prop.Unmarshal(iterator.Value())
//		if err != nil {
//			// An error here would indicate something is very wrong,
//			// the ConsumerRemovalProposal is assumed to be correctly serialized in SetPendingConsumerRemovalProp.
//			panic(fmt.Errorf("failed to unmarshal consumer removal proposal: %w", err))
//		}
//
//		// If current block time is equal to or after stop time, proposal is ready to be executed
//		if !ctx.BlockTime().Before(prop.StopTime) {
//			propsToExecute = append(propsToExecute, prop)
//		} else {
//			// No more proposals to check, since they're stored/ordered by timestamp.
//			break
//		}
//	}
//
//	return propsToExecute
//}

// GetAllPendingConsumerRemovalProps iterates through the pending consumer removal proposals.
//
// Note that the pending consumer removal proposals are stored under keys with the following format:
// PendingCRPKeyPrefix | stopTime.UnixNano() | chainID
// Thus, the returned array is in stopTime order.
func (k Keeper) GetAllPendingConsumerRemovalProps(ctx sdk.Context) (props []types.ConsumerRemovalProposal) {
	store := ctx.KVStore(k.storeKey)
	iterator := storetypes.KVStorePrefixIterator(store, types.PendingCRPKeyPrefix())
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		var prop types.ConsumerRemovalProposal
		err := prop.Unmarshal(iterator.Value())
		if err != nil {
			// An error here would indicate something is very wrong,
			// the ConsumerRemovalProposal is assumed to be correctly serialized in SetPendingConsumerRemovalProp.
			panic(fmt.Errorf("failed to unmarshal consumer removal proposal: %w", err))
		}

		props = append(props, prop)
	}

	return props
}

// StopConsumerChainInCachedCtx stop a consumer chain
// from a given consumer removal proposal in a cached context
func (k Keeper) StopConsumerChainInCachedCtx(ctx sdk.Context, p types.ConsumerRemovalProposal) (cc sdk.Context, writeCache func(), err error) {
	cc, writeCache = ctx.CacheContext()
	err = k.StopConsumerChain(cc, p.ConsumerId, true)
	return
}
