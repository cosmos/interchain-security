package keeper

import (
	"fmt"
	"strconv"

	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	clienttypes "github.com/cosmos/ibc-go/v4/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v4/modules/core/04-channel/types"
	"github.com/cosmos/ibc-go/v4/modules/core/exported"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	utils "github.com/cosmos/interchain-security/x/ccv/utils"
)

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
		k.Logger(ctx).Error("VSCMaturedPacket received on unknown channel",
			"channelID", packet.DestinationChannel,
		)
		panic(fmt.Errorf("VSCMaturedPacket received on unknown channel %s", packet.DestinationChannel))
	}

	if err := k.QueueThrottledVSCMaturedPacketData(ctx, chainID, packet.Sequence, data); err != nil {
		return channeltypes.NewErrorAcknowledgement(fmt.Errorf(
			"failed to queue VSCMatured packet data: %s", err.Error()))
	}

	k.Logger(ctx).Info("VSCMaturedPacket received and enqueued",
		"chainID", chainID,
		"vscID", data.ValsetUpdateId,
	)

	ack := channeltypes.NewResultAcknowledgement([]byte{byte(1)})
	return ack
}

// HandleLeadingVSCMaturedPackets handles all VSCMatured packet data that has been queued this block,
// but does not need to be throttled. The handled data is then removed from the queue.
//
// Note: VSC matured packet data which is queued behind slash packet data CANNOT be
// handled until the leading slash packet data has been handled. This is to maintain
// the "VSC Maturity and Slashing Order" CCV property. If VSC matured packet data DOES NOT
// trail slash packet data for that consumer, it will be handled in this method,
// bypassing HandleThrottleQueues.
func (k Keeper) HandleLeadingVSCMaturedPackets(ctx sdk.Context) {

	for _, chain := range k.GetAllConsumerChains(ctx) {
		leadingVscMatured, ibcSeqNums := k.GetLeadingVSCMaturedData(ctx, chain.ChainId)
		for _, data := range leadingVscMatured {
			k.HandleVSCMaturedPacket(ctx, chain.ChainId, data)
		}
		k.DeleteThrottledPacketData(ctx, chain.ChainId, ibcSeqNums...)
	}
}

// HandleVSCMaturedPacket handles a VSCMatured packet.
//
// Note: This method should only panic for a system critical error like a
// failed marshal/unmarshal, or persistence of critical data.
func (k Keeper) HandleVSCMaturedPacket(ctx sdk.Context, chainID string, data ccv.VSCMaturedPacketData) {
	// iterate over the unbonding operations mapped to (chainID, data.ValsetUpdateId)
	var maturedIds []uint64
	for _, unbondingOp := range k.GetUnbondingOpsFromIndex(ctx, chainID, data.ValsetUpdateId) {
		// Remove consumer chain ID from unbonding op record.
		// Note that RemoveConsumerFromUnbondingOp cannot panic here
		// as all the unbonding ops returned by GetUnbondingOpsFromIndex
		// are retrieved via GetUnbondingOp.
		if k.RemoveConsumerFromUnbondingOp(ctx, unbondingOp.Id, chainID) {
			// Store id of matured unbonding op for later completion of unbonding in staking module
			maturedIds = append(maturedIds, unbondingOp.Id)
		}
	}
	k.AppendMaturedUnbondingOps(ctx, maturedIds)

	// clean up index
	k.DeleteUnbondingOpIndex(ctx, chainID, data.ValsetUpdateId)

	// remove the VSC timeout timestamp for this chainID and vscID
	k.DeleteVscSendTimestamp(ctx, chainID, data.ValsetUpdateId)

	// prune previous consumer validator address that are no longer needed
	k.PruneKeyAssignments(ctx, chainID, data.ValsetUpdateId)

	k.Logger(ctx).Info("VSCMaturedPacket handled",
		"chainID", chainID,
		"vscID", data.ValsetUpdateId,
	)
}

// CompleteMaturedUnbondingOps attempts to complete all matured unbonding operations
func (k Keeper) completeMaturedUnbondingOps(ctx sdk.Context) {
	for _, id := range k.ConsumeMaturedUnbondingOps(ctx) {
		// Attempt to complete unbonding in staking module
		err := k.stakingKeeper.UnbondingCanComplete(ctx, id)
		if err != nil {
			// UnbondingCanComplete fails if the unbonding operation was not found,
			// which means that the state of the x/staking module of cosmos-sdk is invalid.
			panic(fmt.Sprintf("could not complete unbonding op: %s", err.Error()))
		}
		k.Logger(ctx).Debug("unbonding operation matured on all consumers", "opID", id)
	}
}

// OnAcknowledgementPacket handles acknowledgments for sent VSC packets
func (k Keeper) OnAcknowledgementPacket(ctx sdk.Context, packet channeltypes.Packet, ack channeltypes.Acknowledgement) error {
	if err := ack.GetError(); err != "" {
		// The VSC packet data could not be successfully decoded.
		// This should never happen.
		k.Logger(ctx).Error(
			"recv ErrorAcknowledgement",
			"channelID", packet.SourceChannel,
			"error", err,
		)
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
		k.Logger(ctx).Error("packet timeout, unknown channel:", "channelID", packet.SourceChannel)
		// abort transaction
		return sdkerrors.Wrap(
			channeltypes.ErrInvalidChannelState,
			packet.SourceChannel,
		)
	}
	k.Logger(ctx).Info("packet timeout, removing the consumer:", "chainID", chainID)
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

	// try sending VSC packets to all registered consumer chains;
	// if the CCV channel is not established for a consumer chain,
	// the updates will remain queued until the channel is established
	k.SendVSCPackets(ctx)
}

// SendVSCPackets iterates over all registered consumers and sends pending
// VSC packets to the chains with established CCV channels.
// If the CCV channel is not established for a consumer chain,
// the updates will remain queued until the channel is established
func (k Keeper) SendVSCPackets(ctx sdk.Context) {
	for _, chain := range k.GetAllConsumerChains(ctx) {
		// check if CCV channel is established and send
		if channelID, found := k.GetChainToChannel(ctx, chain.ChainId); found {
			k.SendVSCPacketsToChain(ctx, chain.ChainId, channelID)
		}
	}
}

// SendVSCPacketsToChain sends all queued VSC packets to the specified chain
func (k Keeper) SendVSCPacketsToChain(ctx sdk.Context, chainID, channelID string) {
	pendingPackets := k.GetPendingVSCPackets(ctx, chainID)
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
				k.Logger(ctx).Debug("IBC client is expired, cannot send VSC, leaving packet data stored:", "chainID", chainID, "vscid", data.ValsetUpdateId)
				return
			}
			// TODO do not panic if the send fails
			// https://github.com/cosmos/interchain-security/issues/649
			panic(fmt.Errorf("packet could not be sent over IBC: %w", err))
		}
		// set the VSC send timestamp for this packet;
		// note that the VSC send timestamp are set when the packets
		// are actually sent over IBC
		k.SetVscSendTimestamp(ctx, chainID, data.ValsetUpdateId, ctx.BlockTime())
	}
	k.DeletePendingVSCPackets(ctx, chainID)
}

// QueueVSCPackets queues latest validator updates for every registered consumer chain
func (k Keeper) QueueVSCPackets(ctx sdk.Context) {
	valUpdateID := k.GetValidatorSetUpdateId(ctx) // curent valset update ID
	// Get the validator updates from the staking module.
	// Note: GetValidatorUpdates panics if the updates provided by the x/staking module
	// of cosmos-sdk is invalid.
	valUpdates := k.stakingKeeper.GetValidatorUpdates(ctx)

	for _, chain := range k.GetAllConsumerChains(ctx) {
		// Apply the key assignment to the validator updates.
		valUpdates := k.MustApplyKeyAssignmentToValUpdates(ctx, chain.ChainId, valUpdates)

		// check whether there are changes in the validator set;
		// note that this also entails unbonding operations
		// w/o changes in the voting power of the validators in the validator set
		unbondingOps := k.GetUnbondingOpsFromIndex(ctx, chain.ChainId, valUpdateID)
		if len(valUpdates) != 0 || len(unbondingOps) != 0 {
			// construct validator set change packet data
			packet := ccv.NewValidatorSetChangePacketData(valUpdates, valUpdateID, k.ConsumeSlashAcks(ctx, chain.ChainId))
			k.AppendPendingVSCPackets(ctx, chain.ChainId, packet)
			k.Logger(ctx).Info("VSCPacket enqueued:",
				"chainID", chain.ChainId,
				"vscID", valUpdateID,
				"len updates", len(valUpdates),
				"len unbonding ops", len(unbondingOps),
			)
		}
	}

	k.IncrementValidatorSetUpdateId(ctx)
}

// EndBlockCIS contains the EndBlock logic needed for
// the Consumer Initiated Slashing sub-protocol
func (k Keeper) EndBlockCIS(ctx sdk.Context) {
	// set the ValsetUpdateBlockHeight
	blockHeight := uint64(ctx.BlockHeight()) + 1
	valUpdateID := k.GetValidatorSetUpdateId(ctx)
	k.SetValsetUpdateBlockHeight(ctx, valUpdateID, blockHeight)
	k.Logger(ctx).Debug("vscID was mapped to block height", "vscID", valUpdateID, "height", blockHeight)

	// Replenish slash meter if necessary, BEFORE executing slash packet throttling logic.
	// This ensures the meter value is replenished, and not greater than the allowance (max value)
	// for the block, before the throttling logic is executed.
	//
	// Note: CheckForSlashMeterReplenishment contains panics for the following scenarios, any of which should never occur
	// if the protocol is correct and external data is properly validated:
	//
	// - Either SlashMeter or SlashMeterReplenishTimeCandidate have not been set (both of which should be set in InitGenesis, see InitializeSlashMeter).
	// - Params not being set (all of which should be set in InitGenesis).
	// - Marshaling and/or store corruption errors.
	// - Setting invalid slash meter values (see SetSlashMeter).
	k.CheckForSlashMeterReplenishment(ctx)
	// Handle leading vsc matured packets before throttling logic.
	//
	// Note: HandleLeadingVSCMaturedPackets contains panics for the following scenarios, any of which should never occur
	// if the protocol is correct and external data is properly validated:
	//
	// - Marshaling and/or store corruption errors.
	k.HandleLeadingVSCMaturedPackets(ctx)
	// Handle queue entries considering throttling logic.
	//
	// Note: HandleThrottleQueues contains panics for the following scenarios, any of which should never occur
	// if the protocol is correct and external data is properly validated:
	//
	// - SlashMeter has not been set (which should be set in InitGenesis, see InitializeSlashMeter).
	// - Marshaling and/or store corruption errors.
	// - Setting invalid slash meter values (see SetSlashMeter).
	k.HandleThrottleQueues(ctx)
}

// OnRecvSlashPacket delivers a received slash packet, validates it and
// then queues the slash packet as pending if valid.
func (k Keeper) OnRecvSlashPacket(ctx sdk.Context, packet channeltypes.Packet, data ccv.SlashPacketData) exported.Acknowledgement {

	// check that the channel is established, panic if not
	chainID, found := k.GetChannelToChain(ctx, packet.DestinationChannel)
	if !found {
		// SlashPacket packet was sent on a channel different than any of the established CCV channels;
		// this should never happen
		k.Logger(ctx).Error("SlashPacket received on unknown channel",
			"channelID", packet.DestinationChannel,
		)
		panic(fmt.Errorf("SlashPacket received on unknown channel %s", packet.DestinationChannel))
	}

	if err := k.ValidateSlashPacket(ctx, chainID, packet, data); err != nil {
		k.Logger(ctx).Error("invalid slash packet",
			"error", err.Error(),
			"chainID", chainID,
			"consumer cons addr", sdk.ConsAddress(data.Validator.Address).String(),
			"vscID", data.ValsetUpdateId,
			"infractionType", data.Infraction,
		)
		return channeltypes.NewErrorAcknowledgement(err)
	}

	// The slash packet validator address may be known only on the consumer chain,
	// in this case, it must be mapped back to the consensus address on the provider chain
	consumerConsAddr := providertypes.NewConsumerConsAddress(data.Validator.Address)
	providerConsAddr := k.GetProviderAddrFromConsumerAddr(ctx, chainID, consumerConsAddr)

	if data.Infraction == stakingtypes.DoubleSign {
		// getMappedInfractionHeight is already checked in ValidateSlashPacket
		infractionHeight, _ := k.getMappedInfractionHeight(ctx, chainID, data.ValsetUpdateId)

		k.SetSlashLog(ctx, providerConsAddr)
		k.Logger(ctx).Info("SlashPacket received for double-signing",
			"chainID", chainID,
			"consumer cons addr", consumerConsAddr.String(),
			"provider cons addr", providerConsAddr.String(),
			"vscID", data.ValsetUpdateId,
			"infractionHeight", infractionHeight,
		)

		// return successful ack, as an error would result
		// in the consumer closing the CCV channel
		return channeltypes.NewResultAcknowledgement([]byte{byte(1)})
	}

	// Queue a slash entry to the global queue, which will be seen by the throttling logic
	k.QueueGlobalSlashEntry(ctx, providertypes.NewGlobalSlashEntry(
		ctx.BlockTime(),   // recv time
		chainID,           // consumer chain id that sent the packet
		packet.Sequence,   // IBC sequence number of the packet
		providerConsAddr)) // Provider consensus address of val to be slashed

	// Queue slash packet data in the same (consumer chain specific) queue as vsc matured packet data,
	// to enforce order of handling between the two packet data types.
	if err := k.QueueThrottledSlashPacketData(ctx, chainID, packet.Sequence, data); err != nil {
		return channeltypes.NewErrorAcknowledgement(fmt.Errorf("failed to queue slash packet data: %s", err.Error()))
	}

	k.Logger(ctx).Info("slash packet received and enqueued",
		"chainID", chainID,
		"consumer cons addr", consumerConsAddr.String(),
		"provider cons addr", providerConsAddr.String(),
		"vscID", data.ValsetUpdateId,
		"infractionType", data.Infraction,
	)

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

// HandleSlashPacket potentially jails a misbehaving validator for a downtime infraction.
// This method should NEVER be called with a double-sign infraction.
func (k Keeper) HandleSlashPacket(ctx sdk.Context, chainID string, data ccv.SlashPacketData) {

	consumerConsAddr := providertypes.NewConsumerConsAddress(data.Validator.Address)
	// Obtain provider chain consensus address using the consumer chain consensus address
	providerConsAddr := k.GetProviderAddrFromConsumerAddr(ctx, chainID, consumerConsAddr)

	k.Logger(ctx).Debug("handling slash packet",
		"chainID", chainID,
		"consumer cons addr", consumerConsAddr.String(),
		"provider cons addr", providerConsAddr.String(),
		"vscID", data.ValsetUpdateId,
		"infractionType", data.Infraction,
	)

	// Obtain validator from staking keeper
	validator, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, providerConsAddr.ToSdkConsAddr())

	// make sure the validator is not yet unbonded;
	// stakingKeeper.Slash() panics otherwise
	if !found || validator.IsUnbonded() {
		// if validator is not found or is unbonded, drop slash packet and log error.
		// Note that it is impossible for the validator to be not found or unbonded if both the provider
		// and the consumer are following the protocol. Thus if this branch is taken then one or both
		// chains is incorrect, but it is impossible to tell which.
		k.Logger(ctx).Error("validator not found or is unbonded", "validator", providerConsAddr.String())
		return
	}

	// tombstoned validators should not be slashed multiple times.
	if k.slashingKeeper.IsTombstoned(ctx, providerConsAddr.ToSdkConsAddr()) {
		// Log and drop packet if validator is tombstoned.
		k.Logger(ctx).Info(
			"slash packet dropped because validator is already tombstoned",
			"provider cons addr", providerConsAddr.String(),
		)
		return
	}

	infractionHeight, found := k.getMappedInfractionHeight(ctx, chainID, data.ValsetUpdateId)
	if !found {
		k.Logger(ctx).Error("infraction height not found. But was found during slash packet validation")
		// drop packet
		return
	}

	// Note: the SlashPacket is for downtime infraction, as SlashPackets
	// for double-signing infractions are already dropped when received

	// append the validator address to the slash ack for its chain id
	// TODO: consumer cons address should be accepted here
	k.AppendSlashAck(ctx, chainID, consumerConsAddr.String())

	// jail validator
	if !validator.IsJailed() {
		k.stakingKeeper.Jail(ctx, providerConsAddr.ToSdkConsAddr())
		k.Logger(ctx).Info("validator jailed", "provider cons addr", providerConsAddr.String())
		jailTime := ctx.BlockTime().Add(k.slashingKeeper.DowntimeJailDuration(ctx))
		k.slashingKeeper.JailUntil(ctx, providerConsAddr.ToSdkConsAddr(), jailTime)
	}

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

	for _, initTimeoutTimestamp := range k.GetAllInitTimeoutTimestamps(ctx) {
		if currentTimeUint64 > initTimeoutTimestamp.Timestamp {
			// initTimeout expired
			// stop the consumer chain and unlock the unbonding.
			// Note that the CCV channel was not established,
			// thus closeChan is irrelevant
			k.Logger(ctx).Info("about to remove timed out consumer chain - chain was not initialised",
				"chainID", initTimeoutTimestamp.ChainId)
			err := k.StopConsumerChain(ctx, initTimeoutTimestamp.ChainId, false)
			if err != nil {
				if ccv.ErrConsumerChainNotFound.Is(err) {
					// consumer chain not found
					continue
				}
				panic(fmt.Errorf("consumer chain failed to stop: %w", err))
			}
		}
	}

	for _, channelToChain := range k.GetAllChannelToChains(ctx) {
		// Check if the first vscSendTimestamp in iterator + VscTimeoutPeriod
		// exceed the current block time.
		// Checking the first send timestamp for each chain is sufficient since
		// timestamps are ordered by vsc ID.
		// Note: GetFirstVscSendTimestamp panics if the internal state is invalid
		vscSendTimestamp, found := k.GetFirstVscSendTimestamp(ctx, channelToChain.ChainId)
		if found {
			timeoutTimestamp := vscSendTimestamp.Timestamp.Add(k.GetParams(ctx).VscTimeoutPeriod)
			if currentTime.After(timeoutTimestamp) {
				// vscTimeout expired
				// stop the consumer chain and release unbondings
				k.Logger(ctx).Info("about to remove timed out consumer chain - VSCPacket timed out",
					"chainID", channelToChain.ChainId,
					"vscID", vscSendTimestamp.VscId,
				)
				err := k.StopConsumerChain(ctx, channelToChain.ChainId, true)
				if err != nil {
					if ccv.ErrConsumerChainNotFound.Is(err) {
						// consumer chain not found
						continue
					}
					panic(fmt.Errorf("consumer chain failed to stop: %w", err))
				}
			}
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
