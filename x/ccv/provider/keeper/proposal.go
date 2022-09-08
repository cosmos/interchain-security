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
	utils "github.com/cosmos/interchain-security/x/ccv/utils"
	abci "github.com/tendermint/tendermint/abci/types"

	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
)

// HandleConsumerAdditionProposal will receive the consumer chain's client state from the proposal.
// If the spawn time has already passed, then set the consumer chain. Otherwise store the client
// as a pending client, and set once spawn time has passed.
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

// HandleConsumerRemovalProposal stops a consumer chain and releases the outstanding unbonding operations.
// If the stop time hasn't already passed, it stores the proposal as a pending proposal.
func (k Keeper) HandleConsumerRemovalProposal(ctx sdk.Context, p *types.ConsumerRemovalProposal) error {

	if !ctx.BlockTime().Before(p.StopTime) {
		return k.StopConsumerChain(ctx, p.ChainId, false, true)
	}

	k.SetPendingConsumerRemovalProp(ctx, p.ChainId, p.StopTime)
	return nil
}

// StopConsumerChain cleans up the states for the given consumer chain ID and, if the given lockUbd is false,
// it completes the outstanding unbonding operations lock by the consumer chain.
func (k Keeper) StopConsumerChain(ctx sdk.Context, chainID string, lockUbd, closeChan bool) (err error) {
	// check that a client for chainID exists
	if _, found := k.GetConsumerClientId(ctx, chainID); !found {
		// drop the proposal
		return nil
	}

	// clean up states
	k.DeleteConsumerClientId(ctx, chainID)
	k.DeleteLockUnbondingOnTimeout(ctx, chainID)

	// close channel and delete the mappings between chain ID and channel ID
	if channelID, found := k.GetChainToChannel(ctx, chainID); found {
		if closeChan {
			k.CloseChannel(ctx, channelID)
		}
		k.DeleteChainToChannel(ctx, chainID)
		k.DeleteChannelToChain(ctx, channelID)
	}

	// TODO remove pending VSC packets once https://github.com/cosmos/interchain-security/issues/27 is fixed
	k.DeleteInitChainHeight(ctx, chainID)
	k.EmptySlashAcks(ctx, chainID)

	// release unbonding operations if they aren't locked
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
			// clean up index
			k.DeleteUnbondingOpIndex(ctx, chainID, vscID)
			return true
		})
	}
	if err != nil {
		return err
	}

	return nil
}

// CreateConsumerClient will create the CCV client for the given consumer chain. The CCV channel must be built
// on top of the CCV client to ensure connection with the right consumer chain.
func (k Keeper) CreateConsumerClient(ctx sdk.Context, chainID string, initialHeight clienttypes.Height, lockUbdOnTimeout bool) error {
	// check that a client for this chain does not exist
	if _, found := k.GetConsumerClientId(ctx, chainID); found {
		// drop the proposal
		return nil
	}

	// Use the unbonding period on the provider to
	// compute the unbonding period on the consumer
	unbondingTime := utils.ComputeConsumerUnbondingPeriod(k.stakingKeeper.UnbondingTime(ctx))

	// create clientstate by getting template client from parameters and filling in zeroed fields from proposal.
	clientState := k.GetTemplateClient(ctx)
	clientState.ChainId = chainID
	clientState.LatestHeight = initialHeight
	clientState.TrustingPeriod = unbondingTime / utils.TrustingPeriodFraction
	clientState.UnbondingPeriod = unbondingTime

	// TODO: Allow for current validators to set different keys
	consensusState := ibctmtypes.NewConsensusState(ctx.BlockTime(), commitmenttypes.NewMerkleRoot([]byte(ibctmtypes.SentinelRoot)), ctx.BlockHeader().NextValidatorsHash)
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

	// store LockUnbondingOnTimeout flag
	if lockUbdOnTimeout {
		k.SetLockUnbondingOnTimeout(ctx, chainID)
	}
	return nil
}

func (k Keeper) MakeConsumerGenesis(ctx sdk.Context) (gen consumertypes.GenesisState, err error) {
	unbondingTime := k.stakingKeeper.UnbondingTime(ctx)
	height := clienttypes.GetSelfHeight(ctx)

	clientState := k.GetTemplateClient(ctx)
	clientState.ChainId = ctx.ChainID()
	clientState.LatestHeight = height //(+-1???)
	clientState.TrustingPeriod = unbondingTime / utils.TrustingPeriodFraction
	clientState.UnbondingPeriod = unbondingTime

	consState, err := k.clientKeeper.GetSelfConsensusState(ctx, height)
	if err != nil {
		return gen, sdkerrors.Wrapf(clienttypes.ErrConsensusStateNotFound, "error %s getting self consensus state for: %s", err, height)
	}

	gen = *consumertypes.DefaultGenesisState()

	gen.Params.Enabled = true
	gen.NewChain = true
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
func (k Keeper) GetPendingConsumerAdditionProp(ctx sdk.Context, spawnTime time.Time, chainID string) types.ConsumerAdditionProposal {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.PendingCAPKey(spawnTime, chainID))
	if len(bz) == 0 {
		return types.ConsumerAdditionProposal{}
	}
	var clientInfo types.ConsumerAdditionProposal
	k.cdc.MustUnmarshal(bz, &clientInfo)

	return clientInfo
}

func (k Keeper) PendingConsumerAdditionPropIterator(ctx sdk.Context) sdk.Iterator {
	store := ctx.KVStore(k.storeKey)
	return sdk.KVStorePrefixIterator(store, []byte{types.PendingCAPBytePrefix})
}

// IteratePendingConsumerAdditionProps iterates over the pending consumer addition proposals to create
// clients in order and creates the consumer client if the spawn time has passed.
func (k Keeper) IteratePendingConsumerAdditionProps(ctx sdk.Context) {
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
// Note: this method is split out from IteratePendingConsumerAdditionProposals to be easily unit tested.
func (k Keeper) ConsumerAdditionPropsToExecute(ctx sdk.Context) []types.ConsumerAdditionProposal {

	// store the (to be) executed proposals in order
	propsToExecute := []types.ConsumerAdditionProposal{}

	iterator := k.PendingConsumerAdditionPropIterator(ctx)
	defer iterator.Close()

	if !iterator.Valid() {
		return propsToExecute
	}

	for ; iterator.Valid(); iterator.Next() {
		key := iterator.Key()
		spawnTime, _, err := types.ParsePendingCAPKey(key)
		if err != nil {
			panic(fmt.Errorf("failed to parse pending client key: %w", err))
		}

		var prop types.ConsumerAdditionProposal
		k.cdc.MustUnmarshal(iterator.Value(), &prop)

		if !ctx.BlockTime().Before(spawnTime) {
			propsToExecute = append(propsToExecute, prop)
		} else {
			// No more proposals to check, since they're stored/ordered by timestamp.
			break
		}
	}
	return propsToExecute
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

// DeletePendingConsumerRemovalProps deletes the given consumer removal proposals
func (k Keeper) DeletePendingConsumerRemovalProps(ctx sdk.Context, proposals ...types.ConsumerRemovalProposal) {
	store := ctx.KVStore(k.storeKey)

	for _, p := range proposals {
		store.Delete(types.PendingCRPKey(p.StopTime, p.ChainId))
	}
}

func (k Keeper) PendingConsumerRemovalPropIterator(ctx sdk.Context) sdk.Iterator {
	store := ctx.KVStore(k.storeKey)
	return sdk.KVStorePrefixIterator(store, []byte{types.PendingCRPBytePrefix})
}

// IteratePendingConsumerRemovalProps iterates over the pending consumer removal proposals
// in order and stop/removes the chain if the stop time has passed, otherwise it will break out of loop and return.
func (k Keeper) IteratePendingConsumerRemovalProps(ctx sdk.Context) {
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
// Note: this method is split out from IteratePendingConsumerRemovalProps to be easily unit tested.
func (k Keeper) ConsumerRemovalPropsToExecute(ctx sdk.Context) []types.ConsumerRemovalProposal {

	// store the (to be) executed consumer removal proposals in order
	propsToExecute := []types.ConsumerRemovalProposal{}

	iterator := k.PendingConsumerRemovalPropIterator(ctx)
	defer iterator.Close()

	if !iterator.Valid() {
		return propsToExecute
	}

	for ; iterator.Valid(); iterator.Next() {

		key := iterator.Key()
		stopTime, chainID, err := types.ParsePendingCRPKey(key)
		if err != nil {
			panic(fmt.Errorf("failed to parse pending consumer removal proposal key: %w", err))
		}

		if !ctx.BlockTime().Before(stopTime) {
			propsToExecute = append(propsToExecute,
				types.ConsumerRemovalProposal{ChainId: chainID, StopTime: stopTime})
		} else {
			// No more proposals to check, since they're stored/ordered by timestamp.
			break
		}
	}
	return propsToExecute
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
