package keeper

import (
	"errors"
	"fmt"
	"strconv"

	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v8/modules/core/04-channel/types"

	errorsmod "cosmossdk.io/errors"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	abci "github.com/cometbft/cometbft/abci/types"

	providertypes "github.com/cosmos/interchain-security/v6/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/v6/x/ccv/types"
)

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
		if consumerId, ok := k.GetChannelIdToConsumerId(ctx, packet.SourceChannel); ok {
			return k.StopAndPrepareForConsumerRemoval(ctx, consumerId)
		}
		return errorsmod.Wrapf(providertypes.ErrUnknownConsumerChannelId, "recv ErrorAcknowledgement on unknown channel %s", packet.SourceChannel)
	}
	return nil
}

// OnTimeoutPacket aborts the transaction if no chain exists for the destination channel,
// otherwise it stops the chain
func (k Keeper) OnTimeoutPacket(ctx sdk.Context, packet channeltypes.Packet) error {
	consumerId, found := k.GetChannelIdToConsumerId(ctx, packet.SourceChannel)
	if !found {
		k.Logger(ctx).Error("packet timeout, unknown channel:", "channelID", packet.SourceChannel)
		// abort transaction
		return errorsmod.Wrap(
			channeltypes.ErrInvalidChannelState,
			packet.SourceChannel,
		)
	}
	k.Logger(ctx).Info("packet timeout, deleting the consumer:", "consumerId", consumerId)
	return k.StopAndPrepareForConsumerRemoval(ctx, consumerId)
}

// EndBlockVSU contains the EndBlock logic needed for
// the Validator Set Update sub-protocol
func (k Keeper) EndBlockVSU(ctx sdk.Context) ([]abci.ValidatorUpdate, error) {
	// logic to update the provider consensus validator set.
	valUpdates, err := k.ProviderValidatorUpdates(ctx)
	if err != nil {
		return []abci.ValidatorUpdate{}, fmt.Errorf("computing the provider consensus validator set: %w", err)
	}

	if k.BlocksUntilNextEpoch(ctx) == 0 {
		// only queue and send VSCPackets at the boundaries of an epoch

		// collect validator updates
		if err := k.QueueVSCPackets(ctx); err != nil {
			return []abci.ValidatorUpdate{}, fmt.Errorf("queueing consumer validator updates: %w", err)
		}

		// try sending VSC packets to all registered consumer chains;
		// if the CCV channel is not established for a consumer chain,
		// the updates will remain queued until the channel is established
		if err := k.SendVSCPackets(ctx); err != nil {
			return []abci.ValidatorUpdate{}, fmt.Errorf("sending consumer validator updates: %w", err)
		}
	}

	return valUpdates, nil
}

// ProviderValidatorUpdates returns changes in the provider consensus validator set
// from the last block to the current one.
// It retrieves the bonded validators from the staking module and creates a `ConsumerValidator` object for each validator.
// The maximum number of validators is determined by the `maxValidators` parameter.
// The function returns the difference between the current validator set and the next validator set as a list of `abci.ValidatorUpdate` objects.
func (k Keeper) ProviderValidatorUpdates(ctx sdk.Context) ([]abci.ValidatorUpdate, error) {
	// get the bonded validators from the staking module
	bondedValidators, err := k.stakingKeeper.GetBondedValidatorsByPower(ctx)
	if err != nil {
		return []abci.ValidatorUpdate{}, fmt.Errorf("getting bonded validators: %w", err)
	}

	// get the last validator set sent to consensus
	currentValidators, err := k.GetLastProviderConsensusValSet(ctx)
	if err != nil {
		return []abci.ValidatorUpdate{}, fmt.Errorf("getting last provider consensus validator set: %w", err)
	}

	nextValidators := []providertypes.ConsensusValidator{}
	maxValidators := k.GetMaxProviderConsensusValidators(ctx)
	// avoid out of range errors by bounding the max validators to the number of bonded validators
	if maxValidators > int64(len(bondedValidators)) {
		maxValidators = int64(len(bondedValidators))
	}
	for _, val := range bondedValidators[:maxValidators] {
		nextValidator, err := k.CreateProviderConsensusValidator(ctx, val)
		if err != nil {
			return []abci.ValidatorUpdate{},
				fmt.Errorf("creating provider consensus validator(%s): %w", val.OperatorAddress, err)
		}
		nextValidators = append(nextValidators, nextValidator)
	}

	// store the validator set we will send to consensus
	err = k.SetLastProviderConsensusValSet(ctx, nextValidators)
	if err != nil {
		return []abci.ValidatorUpdate{}, fmt.Errorf("setting the last provider consensus validator set: %w", err)
	}

	valUpdates := DiffValidators(currentValidators, nextValidators)

	return valUpdates, nil
}

// BlocksUntilNextEpoch returns the number of blocks until the next epoch starts
// Returns 0 if VSCPackets are sent in the current block,
// which is done in the first block of each epoch.
func (k Keeper) BlocksUntilNextEpoch(ctx sdk.Context) int64 {
	blocksSinceEpochStart := ctx.BlockHeight() % k.GetBlocksPerEpoch(ctx)

	if blocksSinceEpochStart == 0 {
		return 0
	} else {
		return k.GetBlocksPerEpoch(ctx) - blocksSinceEpochStart
	}
}

// SendVSCPackets iterates over all consumers chains with created IBC clients
// and sends pending VSC packets to the chains with established CCV channels.
// If the CCV channel is not established for a consumer chain,
// the updates will remain queued until the channel is established
//
// TODO (mpoke): iterate only over consumers with established channel -- GetAllChannelToConsumers
func (k Keeper) SendVSCPackets(ctx sdk.Context) error {
	for _, consumerId := range k.GetAllConsumersWithIBCClients(ctx) {
		if k.GetConsumerPhase(ctx, consumerId) != providertypes.CONSUMER_PHASE_LAUNCHED {
			// only send VSCPackets to launched chains
			continue
		}

		// check if CCV channel is established and send
		if channelID, found := k.GetConsumerIdToChannelId(ctx, consumerId); found {
			if err := k.SendVSCPacketsToChain(ctx, consumerId, channelID); err != nil {
				return fmt.Errorf("sending VSCPacket to consumer, consumerId(%s): %w", consumerId, err)
			}
		}
	}
	return nil
}

// SendVSCPacketsToChain sends all queued VSC packets to the specified chain
func (k Keeper) SendVSCPacketsToChain(ctx sdk.Context, consumerId, channelId string) error {
	pendingPackets := k.GetPendingVSCPackets(ctx, consumerId)
	for _, data := range pendingPackets {
		// send packet over IBC
		err := ccv.SendIBCPacket(
			ctx,
			k.scopedKeeper,
			k.channelKeeper,
			channelId,          // source channel id
			ccv.ProviderPortID, // source port id
			data.GetBytes(),
			k.GetCCVTimeoutPeriod(ctx),
		)
		if err != nil {
			if errors.Is(err, clienttypes.ErrClientNotActive) {
				// IBC client is expired!
				// leave the packet data stored to be sent once the client is upgraded
				// the client cannot expire during iteration (in the middle of a block)
				k.Logger(ctx).Info("IBC client is expired, cannot send VSC, leaving packet data stored:",
					"consumerId", consumerId,
					"vscid", data.ValsetUpdateId,
				)
				return nil
			}
			// Not able to send packet over IBC!
			k.Logger(ctx).Error("cannot send VSC, removing consumer:", "consumerId", consumerId, "vscid", data.ValsetUpdateId, "err", err.Error())

			err := k.StopAndPrepareForConsumerRemoval(ctx, consumerId)
			if err != nil {
				k.Logger(ctx).Info("consumer chain failed to stop:", "consumerId", consumerId, "error", err.Error())
				// return fmt.Errorf("stopping consumer, consumerId(%s): %w", consumerId, err)
			}
			return nil
		}
	}
	k.DeletePendingVSCPackets(ctx, consumerId)

	return nil
}

// QueueVSCPackets queues latest validator updates for every consumer chain
// with the IBC client created.
//
// TODO (mpoke): iterate only over consumers with established channel -- GetAllChannelToConsumers
func (k Keeper) QueueVSCPackets(ctx sdk.Context) error {
	valUpdateID := k.GetValidatorSetUpdateId(ctx) // current valset update ID

	// get the bonded validators from the staking module
	bondedValidators, err := k.GetLastBondedValidators(ctx)
	if err != nil {
		return fmt.Errorf("getting bonded validators: %w", err)
	}

	// get the provider active validators
	activeValidators, err := k.GetLastProviderConsensusActiveValidators(ctx)
	if err != nil {
		return fmt.Errorf("getting provider active validators: %w", err)
	}

	for _, consumerId := range k.GetAllConsumersWithIBCClients(ctx) {
		if k.GetConsumerPhase(ctx, consumerId) != providertypes.CONSUMER_PHASE_LAUNCHED {
			// only queue VSCPackets to launched chains
			continue
		}

		currentValSet, err := k.GetConsumerValSet(ctx, consumerId)
		if err != nil {
			return fmt.Errorf("getting consumer current validator set, consumerId(%s): %w", consumerId, err)
		}

		// compute consumer next validator set
		valUpdates, err := k.ComputeConsumerNextValSet(ctx, bondedValidators, activeValidators, consumerId, currentValSet)
		if err != nil {
			return fmt.Errorf("computing consumer next validator set, consumerId(%s): %w", consumerId, err)
		}

		// check whether there are changes in the validator set
		if len(valUpdates) != 0 {
			// construct validator set change packet data
			packet := ccv.NewValidatorSetChangePacketData(valUpdates, valUpdateID, k.ConsumeSlashAcks(ctx, consumerId))
			k.AppendPendingVSCPackets(ctx, consumerId, packet)
			k.Logger(ctx).Info("VSCPacket enqueued:",
				"consumerId", consumerId,
				"vscID", valUpdateID,
				"len updates", len(valUpdates),
			)
		}
	}

	k.IncrementValidatorSetUpdateId(ctx)

	return nil
}

// BeginBlockCIS contains the BeginBlock logic needed for the Consumer Initiated Slashing sub-protocol.
func (k Keeper) BeginBlockCIS(ctx sdk.Context) {
	// Replenish slash meter if necessary. This ensures the meter value is replenished before handling any slash packets,
	// and ensures the meter value is not greater than the allowance (max value) for the block.
	//
	// Note: CheckForSlashMeterReplenishment contains panics for the following scenarios, any of which should never occur
	// if the protocol is correct and external data is properly validated:
	//
	// - Either SlashMeter or SlashMeterReplenishTimeCandidate have not been set (both of which should be set in InitGenesis, see InitializeSlashMeter).
	// - Params not being set (all of which should be set in InitGenesis).
	// - Marshaling and/or store corruption errors.
	// - Setting invalid slash meter values (see SetSlashMeter).
	k.CheckForSlashMeterReplenishment(ctx)
}

// EndBlockCIS contains the EndBlock logic needed for
// the Consumer Initiated Slashing sub-protocol
func (k Keeper) EndBlockCIS(ctx sdk.Context) {
	// set the ValsetUpdateBlockHeight
	blockHeight := uint64(ctx.BlockHeight()) + 1
	valUpdateID := k.GetValidatorSetUpdateId(ctx)
	k.SetValsetUpdateBlockHeight(ctx, valUpdateID, blockHeight)
	k.Logger(ctx).Debug("vscID was mapped to block height", "vscID", valUpdateID, "height", blockHeight)

	// prune previous consumer validator addresses that are no longer needed
	for _, consumerId := range k.GetAllConsumersWithIBCClients(ctx) {
		k.PruneKeyAssignments(ctx, consumerId)
	}
}

// OnRecvSlashPacket delivers a received slash packet, validates it and
// then queues the slash packet as pending if valid.
func (k Keeper) OnRecvSlashPacket(
	ctx sdk.Context,
	packet channeltypes.Packet,
	data ccv.SlashPacketData,
) (ccv.PacketAckResult, error) {
	// check that the channel is established, panic if not
	consumerId, found := k.GetChannelIdToConsumerId(ctx, packet.DestinationChannel)
	if !found {
		// SlashPacket packet was sent on a channel different than any of the established CCV channels;
		// this should never happen
		k.Logger(ctx).Error("SlashPacket received on unknown channel",
			"channelID", packet.DestinationChannel,
		)
		panic(fmt.Errorf("SlashPacket received on unknown channel %s", packet.DestinationChannel))
	}

	// validate packet data upon receiving
	if err := data.Validate(); err != nil {
		return nil, errorsmod.Wrapf(err, "error validating SlashPacket data")
	}

	if err := k.ValidateSlashPacket(ctx, consumerId, packet, data); err != nil {
		k.Logger(ctx).Error("invalid slash packet",
			"error", err.Error(),
			"consumerId", consumerId,
			"consumer cons addr", sdk.ConsAddress(data.Validator.Address).String(),
			"vscID", data.ValsetUpdateId,
			"infractionType", data.Infraction,
		)
		return nil, err
	}

	// The slash packet validator address may be known only on the consumer chain,
	// in this case, it must be mapped back to the consensus address on the provider chain
	consumerConsAddr := providertypes.NewConsumerConsAddress(data.Validator.Address)
	providerConsAddr := k.GetProviderAddrFromConsumerAddr(ctx, consumerId, consumerConsAddr)

	if data.Infraction == stakingtypes.Infraction_INFRACTION_DOUBLE_SIGN {
		// getMappedInfractionHeight is already checked in ValidateSlashPacket
		infractionHeight, _ := k.getMappedInfractionHeight(ctx, consumerId, data.ValsetUpdateId)

		k.SetSlashLog(ctx, providerConsAddr)
		k.Logger(ctx).Info("SlashPacket received for double-signing",
			"consumerId", consumerId,
			"consumer cons addr", consumerConsAddr.String(),
			"provider cons addr", providerConsAddr.String(),
			"vscID", data.ValsetUpdateId,
			"infractionHeight", infractionHeight,
		)

		// return successful ack, as an error would result
		// in the consumer closing the CCV channel
		return ccv.V1Result, nil
	}

	// check that the chain is launched
	if k.GetConsumerPhase(ctx, consumerId) != providertypes.CONSUMER_PHASE_LAUNCHED {
		k.Logger(ctx).Info("cannot jail validator on a chain that is not currently launched",
			"consumerId", consumerId,
			"phase", k.GetConsumerPhase(ctx, consumerId),
			"provider cons addr", providerConsAddr.String(),
		)

		// drop packet but return a slash ack
		k.AppendSlashAck(ctx, consumerId, consumerConsAddr.String())

		return ccv.SlashPacketHandledResult, nil
	}

	// check that the validator belongs to the consumer chain valset
	if !k.IsConsumerValidator(ctx, consumerId, providerConsAddr) {
		k.Logger(ctx).Error("cannot jail validator that does not belong on the consumer valset",
			"consumerId", consumerId,
			"provider cons addr", providerConsAddr.String(),
		)

		// drop packet but return a slash ack so that the consumer can send another slash packet
		k.AppendSlashAck(ctx, consumerId, consumerConsAddr.String())

		return ccv.SlashPacketHandledResult, nil
	}

	meter := k.GetSlashMeter(ctx)
	// Return bounce ack if meter is negative in value
	if meter.IsNegative() {
		k.Logger(ctx).Info("SlashPacket received, but meter is negative. Packet will be bounced",
			"consumerId", consumerId,
			"consumer cons addr", consumerConsAddr.String(),
			"provider cons addr", providerConsAddr.String(),
			"vscID", data.ValsetUpdateId,
			"infractionType", data.Infraction,
		)
		return ccv.SlashPacketBouncedResult, nil
	}

	// Subtract voting power that will be jailed/tombstoned from the slash meter,
	// BEFORE handling slash packet.
	meter = meter.Sub(k.GetEffectiveValPower(ctx, providerConsAddr))
	k.SetSlashMeter(ctx, meter)

	k.HandleSlashPacket(ctx, consumerId, data)

	k.Logger(ctx).Info("slash packet received and handled",
		"consumerId", consumerId,
		"consumer cons addr", consumerConsAddr.String(),
		"provider cons addr", providerConsAddr.String(),
		"vscID", data.ValsetUpdateId,
		"infractionType", data.Infraction,
	)

	// Return result ack that the packet was handled successfully
	return ccv.SlashPacketHandledResult, nil
}

// ValidateSlashPacket validates a recv slash packet before it is
// handled or persisted in store. An error is returned if the packet is invalid,
// and an error ack should be relayed to the sender.
func (k Keeper) ValidateSlashPacket(ctx sdk.Context, consumerId string,
	packet channeltypes.Packet, data ccv.SlashPacketData,
) error {
	_, found := k.getMappedInfractionHeight(ctx, consumerId, data.ValsetUpdateId)
	// return error if we cannot find infraction height matching the validator update id
	if !found {
		return fmt.Errorf("cannot find infraction height matching "+
			"the validator update id %d for chain %s", data.ValsetUpdateId, consumerId)
	}

	return nil
}

// HandleSlashPacket potentially jails a misbehaving validator for a downtime infraction.
// This method should NEVER be called with a double-sign infraction.
func (k Keeper) HandleSlashPacket(ctx sdk.Context, consumerId string, data ccv.SlashPacketData) {
	consumerConsAddr := providertypes.NewConsumerConsAddress(data.Validator.Address)
	// Obtain provider chain consensus address using the consumer chain consensus address
	providerConsAddr := k.GetProviderAddrFromConsumerAddr(ctx, consumerId, consumerConsAddr)

	k.Logger(ctx).Debug("HandleSlashPacket",
		"consumerId", consumerId,
		"consumer cons addr", consumerConsAddr.String(),
		"provider cons addr", providerConsAddr.String(),
		"vscID", data.ValsetUpdateId,
		"infractionType", data.Infraction,
	)

	// Obtain validator from staking keeper
	validator, err := k.stakingKeeper.GetValidatorByConsAddr(ctx, providerConsAddr.ToSdkConsAddr())
	if err != nil {
		k.Logger(ctx).Error("validator not found", "validator", providerConsAddr.String(), "error", err)
		return
	}

	// make sure the validator is not yet unbonded;
	// stakingKeeper.Slash() panics otherwise
	if validator.IsUnbonded() {
		// if validator is not found or is unbonded, drop slash packet and log error.
		k.Logger(ctx).Info(
			"HandleSlashPacket - slash packet dropped because validator not found or is unbonded",
			"provider cons addr", providerConsAddr.String(),
		)
		return
	}

	// tombstoned validators should not be slashed multiple times.
	if k.slashingKeeper.IsTombstoned(ctx, providerConsAddr.ToSdkConsAddr()) {
		// Log and drop packet if validator is tombstoned.
		k.Logger(ctx).Info(
			"HandleSlashPacket - slash packet dropped because validator is already tombstoned",
			"provider cons addr", providerConsAddr.String(),
		)
		return
	}

	infractionHeight, found := k.getMappedInfractionHeight(ctx, consumerId, data.ValsetUpdateId)
	if !found {
		k.Logger(ctx).Error(
			"HandleSlashPacket - infraction height not found. But was found during slash packet validation",
			"vscID", data.ValsetUpdateId,
		)
		// drop packet
		return
	}

	// Note: the SlashPacket is for downtime infraction, as SlashPackets
	// for double-signing infractions are already dropped when received

	// append the validator address to the slash ack for its consumer id
	// TODO: consumer cons address should be accepted here
	k.AppendSlashAck(ctx, consumerId, consumerConsAddr.String())

	infractionParams, err := k.GetInfractionParameters(ctx, consumerId)
	if err != nil {
		k.Logger(ctx).Error("failed to get infraction parameters", "err", err.Error())
		return
	}

	if !validator.IsJailed() {
		// slash validator
		_, err = k.stakingKeeper.SlashWithInfractionReason(ctx, providerConsAddr.ToSdkConsAddr(), int64(infractionHeight),
			data.Validator.Power, infractionParams.Downtime.SlashFraction, stakingtypes.Infraction_INFRACTION_DOWNTIME)
		if err != nil {
			k.Logger(ctx).Error("failed to slash vaidator", providerConsAddr.ToSdkConsAddr().String(), "err", err.Error())
			return
		}

		// jail validator
		err := k.stakingKeeper.Jail(ctx, providerConsAddr.ToSdkConsAddr())
		if err != nil {
			k.Logger(ctx).Error("failed to jail vaidator", providerConsAddr.ToSdkConsAddr().String(), "err", err.Error())
			return
		}
		k.Logger(ctx).Info("HandleSlashPacket - validator jailed", "provider cons addr", providerConsAddr.String())

		jailEndTime := ctx.BlockTime().Add(infractionParams.Downtime.JailDuration)
		err = k.slashingKeeper.JailUntil(ctx, providerConsAddr.ToSdkConsAddr(), jailEndTime)
		if err != nil {
			k.Logger(ctx).Error("failed to set jail duration", "err", err.Error())
			return
		}
	}

	ctx.EventManager().EmitEvent(
		sdk.NewEvent(
			providertypes.EventTypeExecuteConsumerChainSlash,
			sdk.NewAttribute(sdk.AttributeKeyModule, providertypes.ModuleName),
			sdk.NewAttribute(ccv.AttributeValidatorAddress, providerConsAddr.String()),
			sdk.NewAttribute(ccv.AttributeInfractionType, data.Infraction.String()),
			sdk.NewAttribute(providertypes.AttributeInfractionHeight, strconv.Itoa(int(infractionHeight))),
			sdk.NewAttribute(ccv.AttributeValSetUpdateID, strconv.Itoa(int(data.ValsetUpdateId))),
		),
	)
}

// getMappedInfractionHeight gets the infraction height mapped from val set ID for the given consumer id
func (k Keeper) getMappedInfractionHeight(ctx sdk.Context,
	consumerId string, valsetUpdateID uint64,
) (height uint64, found bool) {
	if valsetUpdateID == 0 {
		return k.GetInitChainHeight(ctx, consumerId)
	} else {
		return k.GetValsetUpdateBlockHeight(ctx, valsetUpdateID)
	}
}
