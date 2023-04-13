package keeper

import (
	"fmt"
	"strconv"
	"time"

	channeltypes "github.com/cosmos/ibc-go/v4/modules/core/04-channel/types"

	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	clienttypes "github.com/cosmos/ibc-go/v4/modules/core/02-client/types"
	commitmenttypes "github.com/cosmos/ibc-go/v4/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v4/modules/light-clients/07-tendermint/types"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	abci "github.com/tendermint/tendermint/abci/types"
	tmtypes "github.com/tendermint/tendermint/types"

	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
)

// HandleConsumerAdditionProposal will receive the consumer chain's client state from the proposal.
// If the client can be successfully created in a cached context, it stores the proposal as a pending proposal.
//
// Note: This method implements SpawnConsumerChainProposalHandler in spec.
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-hcaprop1
// Spec tag: [CCV-PCF-HCAPROP.1]
func (k Keeper) HandleConsumerAdditionProposal(ctx sdk.Context, p *types.ConsumerAdditionProposal) error {
	// verify the consumer addition proposal execution
	// in cached context and discard the cached writes
	if _, _, err := k.CreateConsumerClientInCachedCtx(ctx, *p); err != nil {
		return err
	}

	k.SetPendingConsumerAdditionProp(ctx, p)

	k.Logger(ctx).Info("consumer addition proposal enqueued",
		"chainID", p.ChainId,
		"title", p.Title,
		"spawn time", p.SpawnTime.UTC(),
	)

	return nil
}

// CreateConsumerClient will create the CCV client for the given consumer chain. The CCV channel must be built
// on top of the CCV client to ensure connection with the right consumer chain.
//
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-crclient1
// Spec tag: [CCV-PCF-CRCLIENT.1]
func (k Keeper) CreateConsumerClient(ctx sdk.Context, prop *types.ConsumerAdditionProposal) error {
	chainID := prop.ChainId
	// check that a client for this chain does not exist
	if _, found := k.GetConsumerClientId(ctx, chainID); found {
		return sdkerrors.Wrap(ccv.ErrDuplicateConsumerChain,
			fmt.Sprintf("cannot create client for existent consumer chain: %s", chainID))
	}

	// Consumers start out with the unbonding period from the consumer addition prop
	consumerUnbondingPeriod := prop.UnbondingPeriod

	// Create client state by getting template client from parameters and filling in zeroed fields from proposal.
	clientState := k.GetTemplateClient(ctx)
	clientState.ChainId = chainID
	clientState.LatestHeight = prop.InitialHeight

	trustPeriod, err := ccv.CalculateTrustPeriod(consumerUnbondingPeriod, k.GetTrustingPeriodFraction(ctx))
	if err != nil {
		return err
	}
	clientState.TrustingPeriod = trustPeriod
	clientState.UnbondingPeriod = consumerUnbondingPeriod

	consumerGen, validatorSetHash, err := k.MakeConsumerGenesis(ctx, prop)
	if err != nil {
		return err
	}
	err = k.SetConsumerGenesis(ctx, chainID, consumerGen)
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
	k.SetConsumerClientId(ctx, chainID, clientID)

	// add the init timeout timestamp for this consumer chain
	ts := ctx.BlockTime().Add(k.GetParams(ctx).InitTimeoutPeriod)
	k.SetInitTimeoutTimestamp(ctx, chainID, uint64(ts.UnixNano()))

	k.Logger(ctx).Info("consumer chain registered (client created)",
		"chainID", chainID,
		"clientID", clientID,
	)

	ctx.EventManager().EmitEvent(
		sdk.NewEvent(
			ccv.EventTypeConsumerClientCreated,
			sdk.NewAttribute(sdk.AttributeKeyModule, types.ModuleName),
			sdk.NewAttribute(ccv.AttributeChainID, chainID),
			sdk.NewAttribute(clienttypes.AttributeKeyClientID, clientID),
			sdk.NewAttribute(ccv.AttributeInitialHeight, prop.InitialHeight.String()),
			sdk.NewAttribute(ccv.AttributeInitializationTimeout, strconv.Itoa(int(ts.UnixNano()))),
			sdk.NewAttribute(ccv.AttributeTrustingPeriod, clientState.TrustingPeriod.String()),
			sdk.NewAttribute(ccv.AttributeUnbondingPeriod, clientState.UnbondingPeriod.String()),
		),
	)

	return nil
}

// HandleConsumerRemovalProposal stops a consumer chain and released the outstanding unbonding operations.
// If the consumer can be successfully stopped in a cached context, it stores the proposal as a pending proposal.
//
// This method implements StopConsumerChainProposalHandler from spec.
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-hcrprop1
// Spec tag: [CCV-PCF-HCRPROP.1]
func (k Keeper) HandleConsumerRemovalProposal(ctx sdk.Context, p *types.ConsumerRemovalProposal) error {
	// verify the consumer removal proposal execution
	// in cached context and discard the cached writes
	if _, _, err := k.StopConsumerChainInCachedCtx(ctx, *p); err != nil {
		return err
	}

	k.SetPendingConsumerRemovalProp(ctx, p)

	k.Logger(ctx).Info("consumer removal proposal enqueued",
		"chainID", p.ChainId,
		"title", p.Title,
		"stop time", p.StopTime.UTC(),
	)

	return nil
}

// StopConsumerChain cleans up the states for the given consumer chain ID and
// completes the outstanding unbonding operations on the consumer chain.
//
// This method implements StopConsumerChain from spec.
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-stcc1
// Spec tag: [CCV-PCF-STCC.1]
func (k Keeper) StopConsumerChain(ctx sdk.Context, chainID string, closeChan bool) (err error) {
	// check that a client for chainID exists
	if _, found := k.GetConsumerClientId(ctx, chainID); !found {
		return sdkerrors.Wrap(ccv.ErrConsumerChainNotFound,
			fmt.Sprintf("cannot stop non-existent consumer chain: %s", chainID))
	}

	// clean up states
	k.DeleteConsumerClientId(ctx, chainID)
	k.DeleteConsumerGenesis(ctx, chainID)
	k.DeleteInitTimeoutTimestamp(ctx, chainID)
	// Note: this call panics if the key assignment state is invalid
	k.DeleteKeyAssignments(ctx, chainID)

	// close channel and delete the mappings between chain ID and channel ID
	if channelID, found := k.GetChainToChannel(ctx, chainID); found {
		if closeChan {
			// Close the channel for the given channel ID on the condition
			// that the channel exists and isn't already in the CLOSED state
			channel, found := k.channelKeeper.GetChannel(ctx, ccv.ProviderPortID, channelID)
			if found && channel.State != channeltypes.CLOSED {
				err := k.chanCloseInit(ctx, channelID)
				if err != nil {
					k.Logger(ctx).Error("channel to consumer chain could not be closed",
						"chainID", chainID,
						"channelID", channelID,
						"error", err.Error(),
					)
				}
			}
		}
		k.DeleteChainToChannel(ctx, chainID)
		k.DeleteChannelToChain(ctx, channelID)

		// delete VSC send timestamps
		k.DeleteVscSendTimestampsForConsumer(ctx, chainID)
	}

	k.DeleteInitChainHeight(ctx, chainID)
	k.DeleteSlashAcks(ctx, chainID)
	k.DeletePendingVSCPackets(ctx, chainID)

	// release unbonding operations
	for _, unbondingOpsIndex := range k.GetAllUnbondingOpIndexes(ctx, chainID) {
		// iterate over the unbonding operations for the current VSC ID
		var maturedIds []uint64
		for _, id := range unbondingOpsIndex.UnbondingOpIds {
			// Remove consumer chain ID from unbonding op record.
			// Note that RemoveConsumerFromUnbondingOp cannot panic here
			// as it is expected that for all UnbondingOpIds in every
			// VscUnbondingOps returned by GetAllUnbondingOpIndexes
			// there is an unbonding op in store that can be retrieved
			// via via GetUnbondingOp.
			if k.RemoveConsumerFromUnbondingOp(ctx, id, chainID) {
				// Store id of matured unbonding op for later completion of unbonding in staking module
				maturedIds = append(maturedIds, id)
			}
		}
		k.AppendMaturedUnbondingOps(ctx, maturedIds)
		k.DeleteUnbondingOpIndex(ctx, chainID, unbondingOpsIndex.VscId)
	}

	// Remove any existing throttling related entries from the global queue,
	// only for this consumer.
	// Note: this call panics if the throttling state is invalid
	k.DeleteGlobalSlashEntriesForConsumer(ctx, chainID)

	if k.GetThrottledPacketDataSize(ctx, chainID) > 0 {
		k.Logger(ctx).Info("There are throttled slash and/or vsc matured packet data instances queued,"+
			" from a consumer that is being removed. This packet data will be thrown out!", "chainID", chainID)
	}

	// Remove all throttled slash packets and vsc matured packets queued for this consumer.
	// Note: queued VSC matured packets can be safely removed from the per-chain queue,
	// since all unbonding operations for this consumer are release above.
	k.DeleteThrottledPacketDataForConsumer(ctx, chainID)

	k.Logger(ctx).Info("consumer chain removed from provider", "chainID", chainID)

	return nil
}

// MakeConsumerGenesis constructs the consumer CCV module part of the genesis state.
func (k Keeper) MakeConsumerGenesis(
	ctx sdk.Context,
	prop *types.ConsumerAdditionProposal,
) (gen consumertypes.GenesisState, nextValidatorsHash []byte, err error) {
	chainID := prop.ChainId
	providerUnbondingPeriod := k.stakingKeeper.UnbondingTime(ctx)
	height := clienttypes.GetSelfHeight(ctx)

	clientState := k.GetTemplateClient(ctx)
	// this is the counter party chain ID for the consumer
	clientState.ChainId = ctx.ChainID()
	// this is the latest height the client was updated at, i.e.,
	// the height of the latest consensus state (see below)
	clientState.LatestHeight = height
	trustPeriod, err := ccv.CalculateTrustPeriod(providerUnbondingPeriod, k.GetTrustingPeriodFraction(ctx))
	if err != nil {
		return gen, nil, sdkerrors.Wrapf(sdkerrors.ErrInvalidHeight, "error %s calculating trusting_period for: %s", err, height)
	}
	clientState.TrustingPeriod = trustPeriod
	clientState.UnbondingPeriod = providerUnbondingPeriod

	consState, err := k.clientKeeper.GetSelfConsensusState(ctx, height)
	if err != nil {
		return gen, nil, sdkerrors.Wrapf(clienttypes.ErrConsensusStateNotFound, "error %s getting self consensus state for: %s", err, height)
	}

	var lastPowers []stakingtypes.LastValidatorPower

	k.stakingKeeper.IterateLastValidatorPowers(ctx, func(addr sdk.ValAddress, power int64) (stop bool) {
		lastPowers = append(lastPowers, stakingtypes.LastValidatorPower{Address: addr.String(), Power: power})
		return false
	})

	initialUpdates := []abci.ValidatorUpdate{}
	for _, p := range lastPowers {
		addr, err := sdk.ValAddressFromBech32(p.Address)
		if err != nil {
			return gen, nil, err
		}

		val, found := k.stakingKeeper.GetValidator(ctx, addr)
		if !found {
			return gen, nil, sdkerrors.Wrapf(stakingtypes.ErrNoValidatorFound, "error getting validator from LastValidatorPowers: %s", err)
		}

		tmProtoPk, err := val.TmConsPublicKey()
		if err != nil {
			return gen, nil, err
		}

		initialUpdates = append(initialUpdates, abci.ValidatorUpdate{
			PubKey: tmProtoPk,
			Power:  p.Power,
		})
	}

	// Apply key assignments to the initial valset.
	initialUpdatesWithConsumerKeys := k.MustApplyKeyAssignmentToValUpdates(ctx, chainID, initialUpdates)

	// Get a hash of the consumer validator set from the update with applied consumer assigned keys
	updatesAsValSet, err := tmtypes.PB2TM.ValidatorUpdates(initialUpdatesWithConsumerKeys)
	if err != nil {
		return gen, nil, fmt.Errorf("unable to create validator set from updates computed from key assignment in MakeConsumerGenesis: %s", err)
	}
	hash := tmtypes.NewValidatorSet(updatesAsValSet).Hash()

	consumerGenesisParams := consumertypes.NewParams(
		true,
		prop.BlocksPerDistributionTransmission,
		"", // distributionTransmissionChannel
		"", // providerFeePoolAddrStr,
		prop.CcvTimeoutPeriod,
		prop.TransferTimeoutPeriod,
		prop.ConsumerRedistributionFraction,
		prop.HistoricalEntries,
		prop.UnbondingPeriod,
		"0.05",
	)

	gen = *consumertypes.NewInitialGenesisState(
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
// the following format: PendingCAPBytePrefix | spawnTime | chainID
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

// BeginBlockInit iterates over the pending consumer addition proposals in order, and creates
// clients for props in which the spawn time has passed. Executed proposals are deleted.
//
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-bblock-init1
// Spec tag:[CCV-PCF-BBLOCK-INIT.1]
func (k Keeper) BeginBlockInit(ctx sdk.Context) {
	propsToExecute := k.GetConsumerAdditionPropsToExecute(ctx)

	for _, prop := range propsToExecute {
		// create consumer client in a cached context to handle errors
		cachedCtx, writeFn, err := k.CreateConsumerClientInCachedCtx(ctx, prop)
		if err != nil {
			// drop the proposal
			ctx.Logger().Info("consumer client could not be created: %w", err)
			continue
		}
		// The cached context is created with a new EventManager so we merge the event
		// into the original context
		ctx.EventManager().EmitEvents(cachedCtx.EventManager().Events())
		// write cache
		writeFn()

		k.Logger(ctx).Info("executed consumer addition proposal",
			"chainID", prop.ChainId,
			"title", prop.Title,
			"spawn time", prop.SpawnTime.UTC(),
		)
	}
	// delete the executed proposals
	k.DeletePendingConsumerAdditionProps(ctx, propsToExecute...)
}

// GetConsumerAdditionPropsToExecute returns the pending consumer addition proposals
// that are ready to be executed, i.e., consumer clients to be created.
// A prop is included in the returned list if its proposed spawn time has passed.
//
// Note: this method is split out from BeginBlockInit to be easily unit tested.
func (k Keeper) GetConsumerAdditionPropsToExecute(ctx sdk.Context) (propsToExecute []types.ConsumerAdditionProposal) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte{types.PendingCAPBytePrefix})
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
// PendingCAPBytePrefix | spawnTime.UnixNano() | chainID
// Thus, the returned array is in spawnTime order. If two proposals have the same spawnTime,
// then they are ordered by chainID.
func (k Keeper) GetAllPendingConsumerAdditionProps(ctx sdk.Context) (props []types.ConsumerAdditionProposal) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte{types.PendingCAPBytePrefix})
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
// the following format: PendingCRPBytePrefix | stopTime | chainID
// Thus, if multiple removal addition proposal for the same chain will pass at
// the same time, then only the last one will be stored.
func (k Keeper) SetPendingConsumerRemovalProp(ctx sdk.Context, prop *types.ConsumerRemovalProposal) {
	store := ctx.KVStore(k.storeKey)
	bz, err := prop.Marshal()
	if err != nil {
		// An error here would indicate something is very wrong
		panic(fmt.Errorf("failed to marshal consumer removal proposal: %w", err))
	}
	store.Set(types.PendingCRPKey(prop.StopTime, prop.ChainId), bz)
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
		store.Delete(types.PendingCRPKey(p.StopTime, p.ChainId))
	}
}

// BeginBlockCCR iterates over the pending consumer removal proposals
// in order and stop/removes the chain if the stop time has passed,
// otherwise it will break out of loop and return. Executed proposals are deleted.
//
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-bblock-ccr1
// Spec tag: [CCV-PCF-BBLOCK-CCR.1]
func (k Keeper) BeginBlockCCR(ctx sdk.Context) {
	propsToExecute := k.GetConsumerRemovalPropsToExecute(ctx)

	for _, prop := range propsToExecute {
		// stop consumer chain in a cached context to handle errors
		cachedCtx, writeFn, err := k.StopConsumerChainInCachedCtx(ctx, prop)
		if err != nil {
			// drop the proposal
			ctx.Logger().Info("consumer chain could not be stopped: %w", err)
			continue
		}
		// The cached context is created with a new EventManager so we merge the event
		// into the original context
		ctx.EventManager().EmitEvents(cachedCtx.EventManager().Events())
		// write cache
		writeFn()

		k.Logger(ctx).Info("executed consumer removal proposal",
			"chainID", prop.ChainId,
			"title", prop.Title,
			"stop time", prop.StopTime.UTC(),
		)
	}
	// delete the executed proposals
	k.DeletePendingConsumerRemovalProps(ctx, propsToExecute...)
}

// GetConsumerRemovalPropsToExecute iterates over the pending consumer removal proposals
// and returns an ordered list of consumer removal proposals to be executed,
// ie. consumer chains to be stopped and removed from the provider chain.
// A prop is included in the returned list if its proposed stop time has passed.
//
// Note: this method is split out from BeginBlockCCR to be easily unit tested.
func (k Keeper) GetConsumerRemovalPropsToExecute(ctx sdk.Context) []types.ConsumerRemovalProposal {
	// store the (to be) executed consumer removal proposals in order
	propsToExecute := []types.ConsumerRemovalProposal{}

	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte{types.PendingCRPBytePrefix})
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		var prop types.ConsumerRemovalProposal
		err := prop.Unmarshal(iterator.Value())
		if err != nil {
			// An error here would indicate something is very wrong,
			// the ConsumerRemovalProposal is assumed to be correctly serialized in SetPendingConsumerRemovalProp.
			panic(fmt.Errorf("failed to unmarshal consumer removal proposal: %w", err))
		}

		// If current block time is equal to or after stop time, proposal is ready to be executed
		if !ctx.BlockTime().Before(prop.StopTime) {
			propsToExecute = append(propsToExecute, prop)
		} else {
			// No more proposals to check, since they're stored/ordered by timestamp.
			break
		}
	}

	return propsToExecute
}

// GetAllPendingConsumerRemovalProps iterates through the pending consumer removal proposals.
//
// Note that the pending consumer removal proposals are stored under keys with the following format:
// PendingCRPBytePrefix | stopTime.UnixNano() | chainID
// Thus, the returned array is in stopTime order.
func (k Keeper) GetAllPendingConsumerRemovalProps(ctx sdk.Context) (props []types.ConsumerRemovalProposal) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte{types.PendingCRPBytePrefix})
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

// CreateConsumerClientInCachedCtx creates a consumer client
// from a given consumer addition proposal in a cached context
func (k Keeper) CreateConsumerClientInCachedCtx(ctx sdk.Context, p types.ConsumerAdditionProposal) (cc sdk.Context, writeCache func(), err error) {
	cc, writeCache = ctx.CacheContext()
	err = k.CreateConsumerClient(cc, &p)
	return
}

// StopConsumerChainInCachedCtx stop a consumer chain
// from a given consumer removal proposal in a cached context
func (k Keeper) StopConsumerChainInCachedCtx(ctx sdk.Context, p types.ConsumerRemovalProposal) (cc sdk.Context, writeCache func(), err error) {
	cc, writeCache = ctx.CacheContext()
	err = k.StopConsumerChain(cc, p.ChainId, true)
	return
}

// HandleEquivocationProposal handles an equivocation proposal.
// Proposal will be accepted if a record in the SlashLog exists for a given validator address.
func (k Keeper) HandleEquivocationProposal(ctx sdk.Context, p *types.EquivocationProposal) error {
	for _, ev := range p.Equivocations {
		if !k.GetSlashLog(ctx, types.NewProviderConsAddress(ev.GetConsensusAddress())) {
			return fmt.Errorf("no equivocation record found for validator %s", ev.GetConsensusAddress().String())
		}
		k.evidenceKeeper.HandleEquivocationEvidence(ctx, ev)
	}
	return nil
}
