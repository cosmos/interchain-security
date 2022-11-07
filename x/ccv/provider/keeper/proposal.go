package keeper

import (
	"fmt"
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

	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
)

// HandleConsumerAdditionProposal will receive the consumer chain's client state from the proposal.
// If the spawn time has already passed, then set the consumer chain. Otherwise store the client
// as a pending client, and set once spawn time has passed.
//
// Note: This method implements SpawnConsumerChainProposalHandler in spec.
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-spccprop1
// Spec tag: [CCV-PCF-SPCCPROP.1]
func (k Keeper) HandleConsumerAdditionProposal(ctx sdk.Context, p *types.ConsumerAdditionProposal) error {
	if !ctx.BlockTime().Before(p.SpawnTime) {
		// lockUbdOnTimeout is set to be false, regardless of what the proposal says, until we can specify and test issues around this use case more thoroughly
		return k.CreateConsumerClient(ctx, p.ChainId, p.InitialHeight, false)
	}

	err := k.SetPendingConsumerAdditionProp(ctx, p)
	if err != nil {
		return err
	}

	return nil
}

// CreateConsumerClient will create the CCV client for the given consumer chain. The CCV channel must be built
// on top of the CCV client to ensure connection with the right consumer chain.
//
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-crclient1
// Spec tag: [CCV-PCF-CRCLIENT.1]
func (k Keeper) CreateConsumerClient(ctx sdk.Context, chainID string,
	initialHeight clienttypes.Height, lockUbdOnTimeout bool) error {

	// check that a client for this chain does not exist
	if _, found := k.GetConsumerClientId(ctx, chainID); found {
		// drop the proposal
		return nil
	}

	// Consumers always start out with the default unbonding period
	consumerUnbondingPeriod := consumertypes.DefaultConsumerUnbondingPeriod

	// Create client state by getting template client from parameters and filling in zeroed fields from proposal.
	clientState := k.GetTemplateClient(ctx)
	clientState.ChainId = chainID
	clientState.LatestHeight = initialHeight
	clientState.TrustingPeriod = consumerUnbondingPeriod / time.Duration(k.GetTrustingPeriodFraction(ctx))
	clientState.UnbondingPeriod = consumerUnbondingPeriod

	// TODO: Allow for current validators to set different keys
	consensusState := ibctmtypes.NewConsensusState(
		ctx.BlockTime(),
		commitmenttypes.NewMerkleRoot([]byte(ibctmtypes.SentinelRoot)),
		ctx.BlockHeader().NextValidatorsHash,
	)

	clientID, err := k.clientKeeper.CreateClient(ctx, clientState, consensusState)
	if err != nil {
		return err
	}
	k.SetConsumerClientId(ctx, chainID, clientID)

	consumerGen, err := k.MakeConsumerGenesis(ctx)
	if err != nil {
		return err
	}
	err = k.SetConsumerGenesis(ctx, chainID, consumerGen)
	if err != nil {
		return err
	}

	// add the init timeout timestamp for this consumer chain
	ts := ctx.BlockTime().Add(k.GetParams(ctx).InitTimeoutPeriod)
	k.SetInitTimeoutTimestamp(ctx, chainID, uint64(ts.UnixNano()))

	// store LockUnbondingOnTimeout flag
	if lockUbdOnTimeout {
		k.SetLockUnbondingOnTimeout(ctx, chainID)
	}
	return nil
}

// HandleConsumerRemovalProposal stops a consumer chain and released the outstanding unbonding operations.
// If the stop time hasn't already passed, it stores the proposal as a pending proposal.
//
// This method implements StopConsumerChainProposalHandler from spec.
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-stccprop1
// Spec tag: [CCV-PCF-STCCPROP.1]
func (k Keeper) HandleConsumerRemovalProposal(ctx sdk.Context, p *types.ConsumerRemovalProposal) error {

	if !ctx.BlockTime().Before(p.StopTime) {
		return k.StopConsumerChain(ctx, p.ChainId, false, true)
	}

	k.SetPendingConsumerRemovalProp(ctx, p.ChainId, p.StopTime)
	return nil
}

// StopConsumerChain cleans up the states for the given consumer chain ID and, if the given lockUbd is false,
// it completes the outstanding unbonding operations lock by the consumer chain.
//
// This method implements StopConsumerChain from spec.
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-stcc1
// Spec tag: [CCV-PCF-STCC.1]
func (k Keeper) StopConsumerChain(ctx sdk.Context, chainID string, lockUbd, closeChan bool) (err error) {
	// check that a client for chainID exists
	if _, found := k.GetConsumerClientId(ctx, chainID); !found {
		// drop the proposal
		return nil
	}

	// clean up states
	k.DeleteConsumerClientId(ctx, chainID)
	k.DeleteConsumerGenesis(ctx, chainID)
	k.DeleteLockUnbondingOnTimeout(ctx, chainID)
	k.DeleteInitTimeoutTimestamp(ctx, chainID)

	// close channel and delete the mappings between chain ID and channel ID
	if channelID, found := k.GetChainToChannel(ctx, chainID); found {
		if closeChan {
			k.CloseChannel(ctx, channelID)
		}
		k.DeleteChainToChannel(ctx, chainID)
		k.DeleteChannelToChain(ctx, channelID)

		// delete VSC send timestamps
		var ids []uint64
		k.IterateVscSendTimestamps(ctx, chainID, func(vscID uint64, ts time.Time) bool {
			ids = append(ids, vscID)
			return true
		})
		for _, vscID := range ids {
			k.DeleteVscSendTimestamp(ctx, chainID, vscID)
		}
	}

	k.DeleteInitChainHeight(ctx, chainID)
	k.ConsumeSlashAcks(ctx, chainID)
	k.ConsumePendingVSCs(ctx, chainID)

	// release unbonding operations if they aren't locked
	var vscIDs []uint64
	if !lockUbd {
		// iterate over the consumer chain's unbonding operation VSC ids
		k.IterateOverUnbondingOpIndex(ctx, chainID, func(vscID uint64, ids []uint64) bool {
			// iterate over the unbonding operations for the current VSC ID
			var maturedIds []uint64
			for _, id := range ids {
				unbondingOp, found := k.GetUnbondingOp(ctx, id)
				if !found {
					err = fmt.Errorf("could not find UnbondingOp according to index - id: %d", id)
					return false
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
					if err := k.SetUnbondingOp(ctx, unbondingOp); err != nil {
						panic(fmt.Errorf("unbonding op could not be persisted: %w", err))
					}
				}
			}
			if err := k.AppendMaturedUnbondingOps(ctx, maturedIds); err != nil {
				panic(fmt.Errorf("mature unbonding ops could not be appended: %w", err))
			}

			vscIDs = append(vscIDs, vscID)
			return true
		})
	}

	if err != nil {
		return err
	}

	// clean up indexes
	for _, id := range vscIDs {
		k.DeleteUnbondingOpIndex(ctx, chainID, id)
	}

	return nil
}

// MakeConsumerGenesis constructs a consumer genesis state.
func (k Keeper) MakeConsumerGenesis(ctx sdk.Context) (gen consumertypes.GenesisState, err error) {
	providerUnbondingPeriod := k.stakingKeeper.UnbondingTime(ctx)
	height := clienttypes.GetSelfHeight(ctx)

	clientState := k.GetTemplateClient(ctx)
	clientState.ChainId = ctx.ChainID() // This will be the counter party chain ID for the consumer
	clientState.LatestHeight = height   //(+-1???)
	clientState.TrustingPeriod = providerUnbondingPeriod / time.Duration(k.GetTrustingPeriodFraction(ctx))
	clientState.UnbondingPeriod = providerUnbondingPeriod

	consState, err := k.clientKeeper.GetSelfConsensusState(ctx, height)
	if err != nil {
		return gen, sdkerrors.Wrapf(clienttypes.ErrConsensusStateNotFound, "error %s getting self consensus state for: %s", err, height)
	}

	gen = *consumertypes.DefaultGenesisState()

	gen.Params.Enabled = true
	gen.NewChain = true
	// This will become the ccv client state for the consumer
	gen.ProviderClientState = clientState
	gen.ProviderConsensusState = consState.(*ibctmtypes.ConsensusState)

	var lastPowers []stakingtypes.LastValidatorPower

	k.stakingKeeper.IterateLastValidatorPowers(ctx, func(addr sdk.ValAddress, power int64) (stop bool) {
		lastPowers = append(lastPowers, stakingtypes.LastValidatorPower{Address: addr.String(), Power: power})
		return false
	})

	updates := []abci.ValidatorUpdate{}

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

		updates = append(updates, abci.ValidatorUpdate{
			PubKey: tmProtoPk,
			Power:  p.Power,
		})
	}

	gen.InitialValSet = updates

	return gen, nil
}

// SetPendingConsumerAdditionProp stores a pending proposal to create a consumer chain client
func (k Keeper) SetPendingConsumerAdditionProp(ctx sdk.Context, clientInfo *types.ConsumerAdditionProposal) error {
	store := ctx.KVStore(k.storeKey)
	bz, err := k.cdc.Marshal(clientInfo)
	if err != nil {
		return err
	}

	store.Set(types.PendingCAPKey(clientInfo.SpawnTime, clientInfo.ChainId), bz)
	return nil
}

// GetPendingConsumerAdditionProp retrieves a pending proposal to create a consumer chain client (by spawn time and chain id)
func (k Keeper) GetPendingConsumerAdditionProp(ctx sdk.Context, spawnTime time.Time,
	chainID string) (prop types.ConsumerAdditionProposal, found bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.PendingCAPKey(spawnTime, chainID))
	if len(bz) == 0 {
		return prop, false
	}
	k.cdc.MustUnmarshal(bz, &prop)

	return prop, true
}

// PendingConsumerAdditionPropIterator returns an iterator for iterating through pending consumer addition proposals
func (k Keeper) PendingConsumerAdditionPropIterator(ctx sdk.Context) sdk.Iterator {
	store := ctx.KVStore(k.storeKey)
	return sdk.KVStorePrefixIterator(store, []byte{types.PendingCAPBytePrefix})
}

// BeginBlockInit iterates over the pending consumer addition proposals in order, and creates
// clients for props in which the spawn time has passed. Executed proposals are deleted.
//
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-bblock-init1
// Spec tag:[CCV-PCF-BBLOCK-INIT.1]
func (k Keeper) BeginBlockInit(ctx sdk.Context) {
	propsToExecute := k.ConsumerAdditionPropsToExecute(ctx)

	for _, prop := range propsToExecute {
		// lockUbdOnTimeout is set to be false, regardless of what the proposal says, until we can specify and test issues around this use case more thoroughly
		err := k.CreateConsumerClient(ctx, prop.ChainId, prop.InitialHeight, false)
		if err != nil {
			panic(fmt.Errorf("consumer client could not be created: %w", err))
		}
	}
	// delete the executed proposals
	k.DeletePendingConsumerAdditionProps(ctx, propsToExecute...)
}

// ConsumerAdditionPropsToExecute iterates over the pending consumer addition proposals
// and returns an ordered list of proposals to be executed, ie. consumer clients to be created.
// A prop is included in the returned list if its proposed spawn time has passed.
//
// Note: this method is split out from BeginBlockInit to be easily unit tested.
func (k Keeper) ConsumerAdditionPropsToExecute(ctx sdk.Context) []types.ConsumerAdditionProposal {

	// store the (to be) executed proposals in order
	propsToExecute := []types.ConsumerAdditionProposal{}

	iterator := k.PendingConsumerAdditionPropIterator(ctx)
	defer iterator.Close()

	k.IteratePendingConsumerAdditionProps(ctx, func(spawnTime time.Time, prop types.ConsumerAdditionProposal) bool {
		if !ctx.BlockTime().Before(spawnTime) {
			propsToExecute = append(propsToExecute, prop)
			return true
		}
		return false
	})

	return propsToExecute
}

func (k Keeper) IteratePendingConsumerAdditionProps(ctx sdk.Context, cb func(spawnTime time.Time, prop types.ConsumerAdditionProposal) bool) {
	iterator := k.PendingConsumerAdditionPropIterator(ctx)
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		key := iterator.Key()
		spawnTime, _, err := types.ParsePendingCAPKey(key)
		if err != nil {
			panic(fmt.Errorf("failed to parse pending client key: %w", err))
		}

		var prop types.ConsumerAdditionProposal
		k.cdc.MustUnmarshal(iterator.Value(), &prop)

		if !cb(spawnTime, prop) {
			return
		}
	}
}

// GetAllConsumerAdditionProps returns all consumer addition proposals separated into matured and pending.
func (k Keeper) GetAllConsumerAdditionProps(ctx sdk.Context) types.ConsumerAdditionProposals {
	props := types.ConsumerAdditionProposals{}

	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte{types.PendingCAPBytePrefix})
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		var prop types.ConsumerAdditionProposal
		k.cdc.MustUnmarshal(iterator.Value(), &prop)

		props.Pending = append(props.Pending, &prop)
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

// SetPendingConsumerRemovalProp stores a pending proposal to remove and stop a consumer chain
func (k Keeper) SetPendingConsumerRemovalProp(ctx sdk.Context, chainID string, timestamp time.Time) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.PendingCRPKey(timestamp, chainID), []byte{})
}

// GetPendingConsumerRemovalProp returns a boolean if a pending consumer removal proposal
// exists for the given consumer chain ID and timestamp
func (k Keeper) GetPendingConsumerRemovalProp(ctx sdk.Context, chainID string, timestamp time.Time) bool {
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

// PendingConsumerRemovalPropIterator returns an iterator for iterating through pending consumer removal proposals
func (k Keeper) PendingConsumerRemovalPropIterator(ctx sdk.Context) sdk.Iterator {
	store := ctx.KVStore(k.storeKey)
	return sdk.KVStorePrefixIterator(store, []byte{types.PendingCRPBytePrefix})
}

// BeginBlockCCR iterates over the pending consumer removal proposals
// in order and stop/removes the chain if the stop time has passed,
// otherwise it will break out of loop and return. Executed proposals are deleted.
//
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-bblock-ccr1
// Spec tag: [CCV-PCF-BBLOCK-CCR.1]
func (k Keeper) BeginBlockCCR(ctx sdk.Context) {
	propsToExecute := k.ConsumerRemovalPropsToExecute(ctx)

	for _, prop := range propsToExecute {
		err := k.StopConsumerChain(ctx, prop.ChainId, false, true)
		if err != nil {
			panic(fmt.Errorf("consumer chain failed to stop: %w", err))
		}
	}
	// delete the executed proposals
	k.DeletePendingConsumerRemovalProps(ctx, propsToExecute...)
}

// ConsumerRemovalPropsToExecute iterates over the pending consumer removal proposals
// and returns an ordered list of consumer removal proposals to be executed,
// ie. consumer chains to be stopped and removed from the provider chain.
// A prop is included in the returned list if its proposed stop time has passed.
//
// Note: this method is split out from BeginBlockCCR to be easily unit tested.
func (k Keeper) ConsumerRemovalPropsToExecute(ctx sdk.Context) []types.ConsumerRemovalProposal {

	// store the (to be) executed consumer removal proposals in order
	propsToExecute := []types.ConsumerRemovalProposal{}

	k.IteratePendingConsumerRemovalProps(ctx, func(stopTime time.Time, prop types.ConsumerRemovalProposal) bool {
		if !ctx.BlockTime().Before(stopTime) {
			propsToExecute = append(propsToExecute, prop)
			return true
		} else {
			// No more proposals to check, since they're stored/ordered by timestamp.
			return false
		}
	})

	return propsToExecute
}

func (k Keeper) IteratePendingConsumerRemovalProps(ctx sdk.Context, cb func(stopTime time.Time, prop types.ConsumerRemovalProposal) bool) {
	iterator := k.PendingConsumerRemovalPropIterator(ctx)
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {

		key := iterator.Key()
		stopTime, chainID, err := types.ParsePendingCRPKey(key)
		if err != nil {
			panic(fmt.Errorf("failed to parse pending consumer removal proposal key: %w", err))
		}

		if !cb(stopTime, types.ConsumerRemovalProposal{ChainId: chainID, StopTime: stopTime}) {
			return
		}
	}
}

// GetAllConsumerRemovalProps returns all consumer removal proposals separated into matured and pending.
func (k Keeper) GetAllConsumerRemovalProps(ctx sdk.Context) types.ConsumerRemovalProposals {
	props := types.ConsumerRemovalProposals{}

	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte{types.PendingCRPBytePrefix})
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		key := iterator.Key()
		stopTime, chainID, err := types.ParsePendingCRPKey(key)
		if err != nil {
			panic(fmt.Errorf("failed to parse pending consumer removal proposal key: %w", err))
		}

		props.Pending = append(props.Pending,
			&types.ConsumerRemovalProposal{ChainId: chainID, StopTime: stopTime})
	}

	return props
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
