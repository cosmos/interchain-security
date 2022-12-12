package keeper

import (
	"fmt"
	"strconv"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	evidencetypes "github.com/cosmos/cosmos-sdk/x/evidence/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	"github.com/cosmos/ibc-go/v3/modules/core/exported"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	utils "github.com/cosmos/interchain-security/x/ccv/utils"
)

func removeStringFromSlice(slice []string, x string) (newSlice []string, numRemoved int) {
	for _, y := range slice {
		if x != y {
			newSlice = append(newSlice, y)
		}
	}

	return newSlice, len(slice) - len(newSlice)
}

// OnRecvVSCMaturedPacket handles a VSCMatured packet
func (k Keeper) OnRecvVSCMaturedPacket(
	ctx sdk.Context,
	packet channeltypes.Packet,
	data ccv.VSCMaturedPacketData,
) exported.Acknowledgement {

	// check that the channel is established, panic if not
	chainID, found := k.GetChannelToChain(ctx, packet.DestinationChannel)
	if !found {
		// VSCMatured packet was sent on a channel different than any of the established CCV channels;
		// this should never happen
		panic(fmt.Errorf("VSCMaturedPacket received on unknown channel %s", packet.DestinationChannel))
	}

	// If no packets are in the per chain queue, immediately handle the vsc matured packet data
	if k.GetPendingPacketDataSize(ctx, chainID) == 0 {
		k.HandleVSCMaturedPacket(ctx, chainID, data)
	} else {
		// Otherwise queue the packet data as pending (behind one or more pending slash packet data instances)
		k.QueuePendingVSCMaturedPacketData(ctx, chainID, packet.Sequence, data)
	}

	ack := channeltypes.NewResultAcknowledgement([]byte{byte(1)})
	return ack
}

// HandleVSCMaturedPacket handles a VSCMatured packet.
//
// Note: This method should only panic for a system critical error like a
// failed marshal/unmarshal, or persistence of critical data.
//
// TODO: Unit test this method.
func (k Keeper) HandleVSCMaturedPacket(ctx sdk.Context, chainID string, data ccv.VSCMaturedPacketData) {
	// iterate over the unbonding operations mapped to (chainID, data.ValsetUpdateId)
	unbondingOps, _ := k.GetUnbondingOpsFromIndex(ctx, chainID, data.ValsetUpdateId)
	var maturedIds []uint64
	for _, unbondingOp := range unbondingOps {
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

	// clean up index
	k.DeleteUnbondingOpIndex(ctx, chainID, data.ValsetUpdateId)

	// remove the VSC timeout timestamp for this chainID and vscID
	k.DeleteVscSendTimestamp(ctx, chainID, data.ValsetUpdateId)

	// prune previous consumer validator address that are no longer needed
	k.PruneKeyAssignments(ctx, chainID, data.ValsetUpdateId)
}

// CompleteMaturedUnbondingOps attempts to complete all matured unbonding operations
func (k Keeper) completeMaturedUnbondingOps(ctx sdk.Context) {
	ids, err := k.ConsumeMaturedUnbondingOps(ctx)
	if err != nil {
		panic(fmt.Sprintf("could not get the list of matured unbonding ops: %s", err.Error()))
	}
	for _, id := range ids {
		// Attempt to complete unbonding in staking module
		err := k.stakingKeeper.UnbondingCanComplete(ctx, id)
		if err != nil {
			panic(fmt.Sprintf("could not complete unbonding op: %s", err.Error()))
		}
	}
}

// OnAcknowledgementPacket handles acknowledgments for sent VSC packets
func (k Keeper) OnAcknowledgementPacket(ctx sdk.Context, packet channeltypes.Packet, ack channeltypes.Acknowledgement) error {
	if err := ack.GetError(); err != "" {
		// The VSC packet data could not be successfully decoded.
		// This should never happen.
		if chainID, ok := k.GetChannelToChain(ctx, packet.SourceChannel); ok {
			// stop consumer chain and release unbonding
			return k.StopConsumerChain(ctx, chainID, false)
		}
		return sdkerrors.Wrapf(providertypes.ErrUnknownConsumerChannelId, "recv ErrorAcknowledgement on unknown channel %s", packet.SourceChannel)
	}
	return nil
}

// OnTimeoutPacket aborts the transaction if no chain exists for the destination channel,
// otherwise it stops the chain
func (k Keeper) OnTimeoutPacket(ctx sdk.Context, packet channeltypes.Packet) error {
	chainID, found := k.GetChannelToChain(ctx, packet.SourceChannel)
	if !found {
		// abort transaction
		return sdkerrors.Wrap(
			channeltypes.ErrInvalidChannelState,
			packet.SourceChannel,
		)
	}
	// stop consumer chain and release unbondings
	return k.StopConsumerChain(ctx, chainID, false)
}

// EndBlockVSU contains the EndBlock logic needed for
// the Validator Set Update sub-protocol
func (k Keeper) EndBlockVSU(ctx sdk.Context) {
	// notify the staking module to complete all matured unbonding ops
	k.completeMaturedUnbondingOps(ctx)

	// collect validator updates
	k.QueueVSCPackets(ctx)

	// try sending packets to all chains
	// if CCV channel is not established for consumer chain
	// the updates will remain queued until the channel is established
	k.SendPackets(ctx)
}

// SendPackets iterates over chains and sends pending packets (VSCs) to
// consumer chains with established CCV channels
// if CCV channel is not established for consumer chain
// the updates will remain queued until the channel is established
func (k Keeper) SendPackets(ctx sdk.Context) {
	k.IterateConsumerChains(ctx, func(ctx sdk.Context, chainID, clientID string) (stop bool) {
		// check if CCV channel is established and send
		if channelID, found := k.GetChainToChannel(ctx, chainID); found {
			k.SendPacketsToChain(ctx, chainID, channelID)
		}
		return false // continue iterating chains
	})
}

// SendPacketsToChain sends all queued packets to the specified chain
func (k Keeper) SendPacketsToChain(ctx sdk.Context, chainID, channelID string) {
	pendingPackets := k.GetPendingPackets(ctx, chainID)
	for _, data := range pendingPackets {
		// send packet over IBC
		err := utils.SendIBCPacket(
			ctx,
			k.scopedKeeper,
			k.channelKeeper,
			channelID,          // source channel id
			ccv.ProviderPortID, // source port id
			data.GetBytes(),
			k.GetCCVTimeoutPeriod(ctx),
		)

		if err != nil {
			if clienttypes.ErrClientNotActive.Is(err) {
				// IBC client is expired!
				// leave the packet data stored to be sent once the client is upgraded
				// the client cannot expire during iteration (in the middle of a block)
				return
			}
			panic(fmt.Errorf("packet could not be sent over IBC: %w", err))
		}
		// set the VSC send timestamp for this packet;
		// note that the VSC send timestamp are set when the packets
		// are actually sent over IBC
		k.SetVscSendTimestamp(ctx, chainID, data.ValsetUpdateId, ctx.BlockTime())
	}
	k.DeletePendingPackets(ctx, chainID)
}

// QueueVSCPackets queues latest validator updates for every registered consumer chain
func (k Keeper) QueueVSCPackets(ctx sdk.Context) {
	valUpdateID := k.GetValidatorSetUpdateId(ctx) // curent valset update ID
	// get the validator updates from the staking module
	valUpdates := k.stakingKeeper.GetValidatorUpdates(ctx)

	k.IterateConsumerChains(ctx, func(ctx sdk.Context, chainID, clientID string) (stop bool) {
		// apply the key assignment to the validator updates
		valUpdates, err := k.ApplyKeyAssignmentToValUpdates(ctx, chainID, valUpdates)
		if err != nil {
			panic(fmt.Sprintf("could not apply key assignment to validator updates for chain %s: %s", chainID, err.Error()))
		}

		// check whether there are changes in the validator set;
		// note that this also entails unbonding operations
		// w/o changes in the voting power of the validators in the validator set
		unbondingOps, _ := k.GetUnbondingOpsFromIndex(ctx, chainID, valUpdateID)
		if len(valUpdates) != 0 || len(unbondingOps) != 0 {
			// construct validator set change packet data
			packet := ccv.NewValidatorSetChangePacketData(valUpdates, valUpdateID, k.ConsumeSlashAcks(ctx, chainID))
			k.AppendPendingPackets(ctx, chainID, packet)
		}
		return false // do not stop the iteration
	})

	k.IncrementValidatorSetUpdateId(ctx)
}

// EndBlockCIS contains the EndBlock logic needed for
// the Consumer Initiated Slashing sub-protocol
func (k Keeper) EndBlockCIS(ctx sdk.Context) {
	// get current ValidatorSetUpdateId
	valUpdateID := k.GetValidatorSetUpdateId(ctx)
	// set the ValsetUpdateBlockHeight
	k.SetValsetUpdateBlockHeight(ctx, valUpdateID, uint64(ctx.BlockHeight()+1))
	// Execute slash packet throttling logic
	k.HandleThrottleQueues(ctx)
	// Replenish slash meter if necessary
	k.CheckForSlashMeterReplenishment(ctx)
}

// OnRecvSlashPacket delivers a received slash packet, validates it and
// then queues the slash packet as pending if valid.
func (k Keeper) OnRecvSlashPacket(ctx sdk.Context, packet channeltypes.Packet, data ccv.SlashPacketData) exported.Acknowledgement {

	// check that the channel is established, panic if not
	chainID, found := k.GetChannelToChain(ctx, packet.DestinationChannel)
	if !found {
		// SlashPacket packet was sent on a channel different than any of the established CCV channels;
		// this should never happen
		panic(fmt.Errorf("SlashPacket received on unknown channel %s", packet.DestinationChannel))
	}

	if err := k.ValidateSlashPacket(ctx, chainID, packet, data); err != nil {
		return channeltypes.NewErrorAcknowledgement(err.Error())
	}

	// The slash packet validator address may be known only on the consumer chain,
	// in this case, it must be mapped back to the consensus address on the provider chain
	consumerConsAddr := sdk.ConsAddress(data.Validator.Address)
	providerConsAddr := k.GetProviderAddrFromConsumerAddr(ctx, chainID, consumerConsAddr)

	// Replace data.Validator.Address with the proper provider chain consensus address,
	// for later use in HandleSlashPacket
	data.Validator.Address = providerConsAddr.Bytes()

	// Queue a slash entry to the global queue, which will be seen by the throttling logic
	k.QueueGlobalSlashEntry(ctx, providertypes.NewGlobalSlashEntry(
		ctx.BlockTime(),   // recv time
		chainID,           // consumer chain id that sent the packet
		packet.Sequence,   // IBC sequence number of the packet
		providerConsAddr)) // Provider consensus address of val to be slashed

	// Queue slash packet data in the same (consumer chain specific) queue as vsc matured packet data,
	// to enforce order of handling between the two packet types.
	k.QueuePendingSlashPacketData(ctx,
		chainID,         // consumer chain id that sent the packet
		packet.Sequence, // IBC sequence number of the packet
		data)

	return channeltypes.NewResultAcknowledgement([]byte{byte(1)})
}

// ValidateSlashPacket validates a recv slash packet before it is
// handled or persisted in store. An error is returned if the packet is invalid,
// and an error ack should be relayed to the sender.
func (k Keeper) ValidateSlashPacket(ctx sdk.Context, chainID string,
	packet channeltypes.Packet, data ccv.SlashPacketData) error {

	_, found := k.getMappedInfractionHeight(ctx, chainID, data.ValsetUpdateId)
	// return error if we cannot find infraction height matching the validator update id
	if !found {
		return fmt.Errorf("cannot find infraction height matching "+
			"the validator update id %d for chain %s", data.ValsetUpdateId, chainID)
	}

	if data.Infraction != stakingtypes.DoubleSign && data.Infraction != stakingtypes.Downtime {
		return fmt.Errorf("invalid infraction type: %s", data.Infraction)
	}

	return nil
}

// HandleSlashPacket potentially slashes, jails and/or tombstones
// a misbehaving validator according to infraction type.
func (k Keeper) HandleSlashPacket(ctx sdk.Context, chainID string, data ccv.SlashPacketData) {

	// Obtain provider chain consensus address from packet data
	// (overwritten with proper provider chain cons address in OnRecvSlashPacket)
	providerConsAddr := sdk.ConsAddress(data.Validator.Address)

	// Obtain validator from staking keeper
	validator, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, data.Validator.Address)

	// make sure the validator is not yet unbonded;
	// stakingKeeper.Slash() panics otherwise
	if !found || validator.IsUnbonded() {
		// if validator is not found or is unbonded, drop slash packet and log error.
		// Note that it is impossible for the validator to be not found or unbonded if both the provider
		// and the consumer are following the protocol. Thus if this branch is taken then one or both
		// chains is incorrect, but it is impossible to tell which.
		k.Logger(ctx).Error("validator not found or is unbonded", "validator", data.Validator.Address)
		return
	}

	// tombstoned validators should not be slashed multiple times.
	if k.slashingKeeper.IsTombstoned(ctx, providerConsAddr) {
		// Log and drop packet if validator is tombstoned.
		k.Logger(ctx).Info(
			"slash packet dropped because validator is already tombstoned",
			"validator cons addr", providerConsAddr,
		)
		return
	}

	// slash and jail validator according to their infraction type
	// and using the provider chain parameters
	var (
		jailTime      time.Time
		slashFraction sdk.Dec
	)

	infractionHeight, found := k.getMappedInfractionHeight(ctx, chainID, data.ValsetUpdateId)
	if !found {
		k.Logger(ctx).Error("infraction height not found. But was found during slash packet validation")
		// drop packet
		return
	}

	switch data.Infraction {
	case stakingtypes.Downtime:
		// set the downtime slash fraction and duration
		// then append the validator address to the slash ack for its chain id
		slashFraction = k.slashingKeeper.SlashFractionDowntime(ctx)
		jailTime = ctx.BlockTime().Add(k.slashingKeeper.DowntimeJailDuration(ctx))
		k.AppendSlashAck(ctx, chainID, providerConsAddr.String())
	case stakingtypes.DoubleSign:
		// set double-signing slash fraction and infinite jail duration
		// then tombstone the validator
		slashFraction = k.slashingKeeper.SlashFractionDoubleSign(ctx)
		jailTime = evidencetypes.DoubleSignJailEndTime
		k.slashingKeeper.Tombstone(ctx, providerConsAddr)
	}

	// slash validator
	k.stakingKeeper.Slash(
		ctx,
		providerConsAddr,
		int64(infractionHeight),
		data.Validator.Power,
		slashFraction,
		data.Infraction,
	)

	// jail validator
	if !validator.IsJailed() {
		k.stakingKeeper.Jail(ctx, providerConsAddr)
	}
	k.slashingKeeper.JailUntil(ctx, providerConsAddr, jailTime)

	ctx.EventManager().EmitEvent(
		sdk.NewEvent(
			ccv.EventTypeExecuteConsumerChainSlash,
			sdk.NewAttribute(sdk.AttributeKeyModule, providertypes.ModuleName),
			sdk.NewAttribute(ccv.AttributeValidatorAddress, providerConsAddr.String()),
			sdk.NewAttribute(ccv.AttributeInfractionType, data.Infraction.String()),
			sdk.NewAttribute(ccv.AttributeInfractionHeight, strconv.Itoa(int(infractionHeight))),
			sdk.NewAttribute(ccv.AttributeValSetUpdateID, strconv.Itoa(int(data.ValsetUpdateId))),
		),
	)
}

// EndBlockCCR contains the EndBlock logic needed for
// the Consumer Chain Removal sub-protocol
func (k Keeper) EndBlockCCR(ctx sdk.Context) {
	currentTime := ctx.BlockTime()
	currentTimeUint64 := uint64(currentTime.UnixNano())

	// iterate over initTimeoutTimestamps
	var chainIdsToRemove []string
	k.IterateInitTimeoutTimestamp(ctx, func(chainID string, ts uint64) (stop bool) {
		if currentTimeUint64 > ts {
			// initTimeout expired
			chainIdsToRemove = append(chainIdsToRemove, chainID)
		}
		// continue to iterate through all timed out consumers
		return false
	})
	// remove consumers that timed out
	for _, chainID := range chainIdsToRemove {
		// stop the consumer chain and unlock the unbonding.
		// Note that the CCV channel was not established,
		// thus closeChan is irrelevant
		err := k.StopConsumerChain(ctx, chainID, false)
		if err != nil {
			panic(fmt.Errorf("consumer chain failed to stop: %w", err))
		}
	}

	// empty slice
	chainIdsToRemove = nil

	// Iterate over all consumers with established CCV channels and
	// check if the first vscSendTimestamp in iterator + VscTimeoutPeriod
	// exceed the current block time.
	// Checking the first send timestamp for each chain is sufficient since
	// timestamps are ordered by vsc ID.
	k.IterateChannelToChain(ctx, func(ctx sdk.Context, _, chainID string) (stop bool) {
		k.IterateVscSendTimestamps(ctx, chainID, func(_ uint64, ts time.Time) (stop bool) {
			timeoutTimestamp := ts.Add(k.GetParams(ctx).VscTimeoutPeriod)
			if currentTime.After(timeoutTimestamp) {
				// vscTimeout expired
				chainIdsToRemove = append(chainIdsToRemove, chainID)
			}
			// break iteration since the send timestamps are sorted in descending order
			return true
		})
		// continue to iterate through all consumers
		return false
	})
	// remove consumers that timed out
	for _, chainID := range chainIdsToRemove {
		// stop the consumer chain and release unbondings
		err := k.StopConsumerChain(ctx, chainID, true)
		if err != nil {
			panic(fmt.Errorf("consumer chain failed to stop: %w", err))
		}
	}
}

// getMappedInfractionHeight gets the infraction height mapped from val set ID for the given chain ID
func (k Keeper) getMappedInfractionHeight(ctx sdk.Context,
	chainID string, valsetUpdateID uint64) (height uint64, found bool) {

	if valsetUpdateID == 0 {
		return k.GetInitChainHeight(ctx, chainID)
	} else {
		return k.GetValsetUpdateBlockHeight(ctx, valsetUpdateID)
	}
}
