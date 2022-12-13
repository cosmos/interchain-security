package keeper

import (
	"fmt"
	"strconv"
	"time"

	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"

	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	commitmenttypes "github.com/cosmos/ibc-go/v3/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	abci "github.com/tendermint/tendermint/abci/types"
	tmtypes "github.com/tendermint/tendermint/types"

	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
)

// HandleConsumerAdditionProposal will receive the consumer chain's client state from the proposal.
// If the spawn time has already passed, then set the consumer chain. Otherwise store the client
// as a pending client, and set once spawn time has passed.
//
// Note: This method implements SpawnConsumerChainProposalHandler in spec.
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-hcaprop1
// Spec tag: [CCV-PCF-HCAPROP.1]
func (k Keeper) HandleConsumerAdditionProposal(ctx sdk.Context, p *types.ConsumerAdditionProposal) error {
	if !ctx.BlockTime().Before(p.SpawnTime) {
		return k.CreateConsumerClient(ctx, p)
	}

	k.SetPendingConsumerAdditionProp(ctx, p)
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
	if _, found := k.GetConsumerClientId(ctx, prop.ChainId); found {
		// drop the proposal
		return nil
	}

	// Consumers always start out with the default unbonding period
	consumerUnbondingPeriod := prop.UnbondingPeriod

	// Create client state by getting template client from parameters and filling in zeroed fields from proposal.
	clientState := k.GetTemplateClient(ctx)
	clientState.ChainId = prop.ChainId
	clientState.LatestHeight = prop.InitialHeight
	clientState.TrustingPeriod = consumerUnbondingPeriod / time.Duration(k.GetTrustingPeriodFraction(ctx))
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
// If the stop time hasn't already passed, it stores the proposal as a pending proposal.
//
// This method implements StopConsumerChainProposalHandler from spec.
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-hcrprop1
// Spec tag: [CCV-PCF-HCRPROP.1]
func (k Keeper) HandleConsumerRemovalProposal(ctx sdk.Context, p *types.ConsumerRemovalProposal) error {

	if !ctx.BlockTime().Before(p.StopTime) {
		return k.StopConsumerChain(ctx, p.ChainId, true)
	}

	k.SetPendingConsumerRemovalProp(ctx, p)
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
		// drop the proposal
		return nil
	}

	// clean up states
	k.DeleteConsumerClientId(ctx, chainID)
	k.DeleteConsumerGenesis(ctx, chainID)
	k.DeleteInitTimeoutTimestamp(ctx, chainID)
	k.DeleteKeyAssignments(ctx, chainID)

	// close channel and delete the mappings between chain ID and channel ID
	if channelID, found := k.GetChainToChannel(ctx, chainID); found {
		if closeChan {
			k.CloseChannel(ctx, channelID)
		}
		k.DeleteChainToChannel(ctx, chainID)
		k.DeleteChannelToChain(ctx, channelID)

		// delete VSC send timestamps
		var ids []uint64
		k.IterateVscSendTimestamps(ctx, chainID, func(vscID uint64, ts time.Time) (stop bool) {
			ids = append(ids, vscID)
			return false // do not stop the iteration
		})
		for _, vscID := range ids {
			k.DeleteVscSendTimestamp(ctx, chainID, vscID)
		}
	}

	k.DeleteInitChainHeight(ctx, chainID)
	k.ConsumeSlashAcks(ctx, chainID)
	k.DeletePendingVSCPackets(ctx, chainID)

	// release unbonding operations
	var vscIDs []uint64
	// iterate over the consumer chain's unbonding operation VSC ids
	k.IterateUnbondingOpIndex(ctx, chainID, func(vscID uint64, ids []uint64) (stop bool) {
		// iterate over the unbonding operations for the current VSC ID
		var maturedIds []uint64
		for _, id := range ids {
			unbondingOp, found := k.GetUnbondingOp(ctx, id)
			if !found {
				err = fmt.Errorf("could not find UnbondingOp according to index - id: %d", id)
				return true // stop the iteration
			}
			// remove consumer chain ID from unbonding op record
			unbondingOp.UnbondingConsumerChains, _ = removeStringFromSlice(unbondingOp.UnbondingConsumerChains, chainID)

			// If unbonding op is completely unbonded from all relevant consumer chains
			if len(unbondingOp.UnbondingConsumerChains) == 0 {
				// Store id of matured unbonding op for later completion of unbonding in staking module
				maturedIds = append(maturedIds, unbondingOp.Id)
				// Delete unbonding op
				k.DeleteUnbondingOp(ctx, unbondingOp.Id)
			} else {
				k.SetUnbondingOp(ctx, unbondingOp)
			}
		}
		k.AppendMaturedUnbondingOps(ctx, maturedIds)

		vscIDs = append(vscIDs, vscID)
		return false // do not stop the iteration
	})

	if err != nil {
		return err
	}

	// clean up indexes
	for _, id := range vscIDs {
		k.DeleteUnbondingOpIndex(ctx, chainID, id)
	}

	return nil
}

// MakeConsumerGenesis constructs the consumer CCV module part of the genesis state.
func (k Keeper) MakeConsumerGenesis(ctx sdk.Context, prop *types.ConsumerAdditionProposal) (gen consumertypes.GenesisState, nextValidatorsHash []byte, err error) {
	chainID := prop.ChainId
	providerUnbondingPeriod := k.stakingKeeper.UnbondingTime(ctx)
	height := clienttypes.GetSelfHeight(ctx)

	clientState := k.GetTemplateClient(ctx)
	// this is the counter party chain ID for the consumer
	clientState.ChainId = ctx.ChainID()
	// this is the latest height the client was updated at, i.e.,
	// the height of the latest consensus state (see below)
	clientState.LatestHeight = height
	clientState.TrustingPeriod = providerUnbondingPeriod / time.Duration(k.GetTrustingPeriodFraction(ctx))
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
			panic(err)
		}

		val, found := k.stakingKeeper.GetValidator(ctx, addr)
		if !found {
			panic("Validator from LastValidatorPowers not found in staking keeper")
		}

		tmProtoPk, err := val.TmConsPublicKey()
		if err != nil {
			panic(err)
		}

		initialUpdates = append(initialUpdates, abci.ValidatorUpdate{
			PubKey: tmProtoPk,
			Power:  p.Power,
		})
	}

	// apply key assignments to the initial valset
	initialUpdatesWithConsumerKeys, err := k.ApplyKeyAssignmentToValUpdates(ctx, chainID, initialUpdates)
	if err != nil {
		panic("unable to apply key assignments to the initial valset")
	}

	// Get a hash of the consumer validator set from the update with applied consumer assigned keys
	updatesAsValSet, err := tmtypes.PB2TM.ValidatorUpdates(initialUpdatesWithConsumerKeys)
	if err != nil {
		panic("unable to create validator set from updates computed from key assignment in MakeConsumerGenesis")
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
func (k Keeper) SetPendingConsumerAdditionProp(ctx sdk.Context, clientInfo *types.ConsumerAdditionProposal) {
	store := ctx.KVStore(k.storeKey)
	bz, err := k.cdc.Marshal(clientInfo)
	if err != nil {
		panic(fmt.Errorf("consumer addition proposal could not be marshaled: %w", err))
	}
	store.Set(types.PendingCAPKey(clientInfo.SpawnTime, clientInfo.ChainId), bz)
}

// GetPendingConsumerAdditionProp retrieves a pending consumer addition proposal
// by spawn time and chain id.
//
// Note: this method is only used in testing
func (k Keeper) GetPendingConsumerAdditionProp(
	ctx sdk.Context,
	spawnTime time.Time,
	chainID string,
) (prop types.ConsumerAdditionProposal, found bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.PendingCAPKey(spawnTime, chainID))
	if len(bz) == 0 {
		return prop, false
	}
	k.cdc.MustUnmarshal(bz, &prop)

	return prop, true
}

// DeletePendingConsumerAdditionProps deletes the given consumer addition proposals
func (k Keeper) DeletePendingConsumerAdditionProps(ctx sdk.Context, proposals ...types.ConsumerAdditionProposal) {
	store := ctx.KVStore(k.storeKey)
	for _, p := range proposals {
		store.Delete(types.PendingCAPKey(p.SpawnTime, p.ChainId))
	}
}

// BeginBlockInit iterates over the pending consumer addition proposals in order, and creates
// clients for props in which the spawn time has passed. Executed proposals are deleted.
//
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-bblock-init1
// Spec tag:[CCV-PCF-BBLOCK-INIT.1]
func (k Keeper) BeginBlockInit(ctx sdk.Context) {
	propsToExecute := k.GetConsumerAdditionPropsToExecute(ctx)

	for _, prop := range propsToExecute {
		p := prop
		err := k.CreateConsumerClient(ctx, &p)
		if err != nil {
			panic(fmt.Errorf("consumer client could not be created: %w", err))
		}
	}
	// delete the executed proposals
	k.DeletePendingConsumerAdditionProps(ctx, propsToExecute...)
}

// GetConsumerAdditionPropsToExecute returns the pending consumer addition proposals
// that are ready to be executed, i.e., consumer clients to be created.
// A prop is included in the returned list if its proposed spawn time has passed.
//
// Note: this method is split out from BeginBlockInit to be easily unit tested.
func (k Keeper) GetConsumerAdditionPropsToExecute(ctx sdk.Context) []types.ConsumerAdditionProposal {
	propsToExecute := []types.ConsumerAdditionProposal{}
	k.IteratePendingConsumerAdditionProps(ctx, func(prop types.ConsumerAdditionProposal) (stop bool) {
		if !ctx.BlockTime().Before(prop.SpawnTime) {
			propsToExecute = append(propsToExecute, prop)
			return false // do not stop the iteration
		}
		// stop iteration; proposals are ordered by spawn time,
		// so no additional pending props are ready to act upon
		return true
	})
	return propsToExecute
}

// IteratePendingConsumerAdditionProps iterates through the pending consumer addition proposals.
//
// Note that the pending consumer addition proposals are stored under keys with the following format:
// PendingCAPBytePrefix | spawnTime | chainID
// Thus, the iteration is in ascending order of spawnTimes.
func (k Keeper) IteratePendingConsumerAdditionProps(
	ctx sdk.Context,
	cb func(prop types.ConsumerAdditionProposal) (stop bool),
) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte{types.PendingCAPBytePrefix})
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		var prop types.ConsumerAdditionProposal
		k.cdc.MustUnmarshal(iterator.Value(), &prop)

		stop := cb(prop)
		if stop {
			break
		}
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
	bz, err := k.cdc.Marshal(prop)
	if err != nil {
		panic(fmt.Errorf("consumer removal proposal could not be marshaled: %w", err))
	}
	store.Set(types.PendingCRPKey(prop.StopTime, prop.ChainId), bz)
}

// IsPendingConsumerRemovalProp checks whether a pending consumer removal proposal
// exists for the given consumer chain ID and stopTime
//
// Note: this method is only used in testing
func (k Keeper) IsPendingConsumerRemovalProp(ctx sdk.Context, chainID string, stopTime time.Time) bool {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.PendingCRPKey(stopTime, chainID))

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
		err := k.StopConsumerChain(ctx, prop.ChainId, true)
		if err != nil {
			panic(fmt.Errorf("consumer chain failed to stop: %w", err))
		}
	}
	// delete the executed proposals
	k.DeletePendingConsumerRemovalProps(ctx, propsToExecute...)
}

// GetConsumerRemovalPropsToExecute returns the pending consumer removal proposals
// that are ready to be executed, i.e., consumer chains to be stopped and removed
// from the provider chain.
// A prop is included in the returned list if its proposed stop time has passed.
//
// Note: this method is split out from BeginBlockCCR to be easily unit tested.
func (k Keeper) GetConsumerRemovalPropsToExecute(ctx sdk.Context) []types.ConsumerRemovalProposal {
	propsToExecute := []types.ConsumerRemovalProposal{}

	k.IteratePendingConsumerRemovalProps(ctx, func(prop types.ConsumerRemovalProposal) (stop bool) {
		if !ctx.BlockTime().Before(prop.StopTime) {
			propsToExecute = append(propsToExecute, prop)
			return false // do not stop the iteration
		}
		// stop iteration; proposals are ordered by stop time,
		// so no additional pending props are ready to act upon
		return true
	})

	return propsToExecute
}

// IteratePendingConsumerRemovalProps iterates through the pending consumer removal proposals.
//
// Note that the pending consumer removal proposals are stored under keys with the following format:
// PendingCRPBytePrefix | stopTime | chainID
// Thus, the iteration is in ascending order of stopTimes.
func (k Keeper) IteratePendingConsumerRemovalProps(
	ctx sdk.Context,
	cb func(prop types.ConsumerRemovalProposal) (stop bool),
) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte{types.PendingCRPBytePrefix})
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		var prop types.ConsumerRemovalProposal
		k.cdc.MustUnmarshal(iterator.Value(), &prop)

		stop := cb(prop)
		if stop {
			break
		}
	}
}

// CloseChannel closes the channel for the given channel ID on the condition
// that the channel exists and isn't already in the CLOSED state
func (k Keeper) CloseChannel(ctx sdk.Context, channelID string) {
	channel, found := k.channelKeeper.GetChannel(ctx, ccv.ProviderPortID, channelID)
	if found && channel.State != channeltypes.CLOSED {
		err := k.chanCloseInit(ctx, channelID)
		if err != nil {
			panic(fmt.Errorf("channel (id: %s) could not be closed: %w", channelID, err))
		}
	}
}
