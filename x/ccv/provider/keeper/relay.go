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

	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	providertypes "github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/v5/x/ccv/types"
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
		if chainID, ok := k.GetChannelIdToConsumerId(ctx, packet.SourceChannel); ok {
			// stop consumer chain and release unbonding
			return k.StopConsumerChain(ctx, chainID, false)
		}
		return errorsmod.Wrapf(providertypes.ErrUnknownConsumerChannelId, "recv ErrorAcknowledgement on unknown channel %s", packet.SourceChannel)
	}
	return nil
}

// OnTimeoutPacket aborts the transaction if no chain exists for the destination channel,
// otherwise it stops the chain
func (k Keeper) OnTimeoutPacket(ctx sdk.Context, packet channeltypes.Packet) error {
	chainID, found := k.GetChannelIdToConsumerId(ctx, packet.SourceChannel)
	if !found {
		k.Logger(ctx).Error("packet timeout, unknown channel:", "channelID", packet.SourceChannel)
		// abort transaction
		return errorsmod.Wrap(
			channeltypes.ErrInvalidChannelState,
			packet.SourceChannel,
		)
	}
	k.Logger(ctx).Info("packet timeout, removing the consumer:", "consumerId", chainID)
	// stop consumer chain and release unbondings
	return k.StopConsumerChain(ctx, chainID, false)
}

// EndBlockVSU contains the EndBlock logic needed for
// the Validator Set Update sub-protocol
func (k Keeper) EndBlockVSU(ctx sdk.Context) ([]abci.ValidatorUpdate, error) {
	// logic to update the provider consensus validator set.
	valUpdates := k.ProviderValidatorUpdates(ctx)

	if k.BlocksUntilNextEpoch(ctx) == 0 {
		// only queue and send VSCPackets at the boundaries of an epoch

		// collect validator updates
		k.QueueVSCPackets(ctx)

		// try sending VSC packets to all registered consumer chains;
		// if the CCV channel is not established for a consumer chain,
		// the updates will remain queued until the channel is established
		k.SendVSCPackets(ctx)
	}

	return valUpdates, nil
}

// ProviderValidatorUpdates returns changes in the provider consensus validator set
// from the last block to the current one.
// It retrieves the bonded validators from the staking module and creates a `ConsumerValidator` object for each validator.
// The maximum number of validators is determined by the `maxValidators` parameter.
// The function returns the difference between the current validator set and the next validator set as a list of `abci.ValidatorUpdate` objects.
func (k Keeper) ProviderValidatorUpdates(ctx sdk.Context) []abci.ValidatorUpdate {
	// get the bonded validators from the staking module
	bondedValidators, err := k.stakingKeeper.GetBondedValidatorsByPower(ctx)
	if err != nil {
		panic(fmt.Errorf("failed to get bonded validators: %w", err))
	}

	// get the last validator set sent to consensus
	currentValidators, err := k.GetLastProviderConsensusValSet(ctx)
	if err != nil {
		panic(fmt.Errorf("failed to get last provider consensus validator set: %w", err))
	}

	nextValidators := []types.ConsensusValidator{}
	maxValidators := k.GetMaxProviderConsensusValidators(ctx)
	// avoid out of range errors by bounding the max validators to the number of bonded validators
	if maxValidators > int64(len(bondedValidators)) {
		maxValidators = int64(len(bondedValidators))
	}
	for _, val := range bondedValidators[:maxValidators] {
		nextValidator, err := k.CreateProviderConsensusValidator(ctx, val)
		if err != nil {
			k.Logger(ctx).Error("error when creating provider consensus validator", "error", err, "validator", val)
			continue
		}
		nextValidators = append(nextValidators, nextValidator)
	}

	// store the validator set we will send to consensus
	k.SetLastProviderConsensusValSet(ctx, nextValidators)

	valUpdates := DiffValidators(currentValidators, nextValidators)

	return valUpdates
}

// BlocksUntilNextEpoch returns the number of blocks until the next epoch starts
// Returns 0 if VSCPackets are sent in the current block,
// which is done in the first block of each epoch.
func (k Keeper) BlocksUntilNextEpoch(ctx sdk.Context) int64 {
	blocksSinceEpochStart := ctx.BlockHeight() % k.GetBlocksPerEpoch(ctx)

	if blocksSinceEpochStart == 0 {
		return 0
	} else {
		return int64(k.GetBlocksPerEpoch(ctx) - blocksSinceEpochStart)
	}
}

// SendVSCPackets iterates over all registered consumers and sends pending
// VSC packets to the chains with established CCV channels.
// If the CCV channel is not established for a consumer chain,
// the updates will remain queued until the channel is established
func (k Keeper) SendVSCPackets(ctx sdk.Context) {
	for _, chainID := range k.GetAllRegisteredConsumerIds(ctx) {
		// check if CCV channel is established and send
		if channelID, found := k.GetConsumerIdToChannelId(ctx, chainID); found {
			k.SendVSCPacketsToChain(ctx, chainID, channelID)
		}
	}
}

// SendVSCPacketsToChain sends all queued VSC packets to the specified chain
func (k Keeper) SendVSCPacketsToChain(ctx sdk.Context, chainID, channelID string) {
	pendingPackets := k.GetPendingVSCPackets(ctx, chainID)
	for _, data := range pendingPackets {
		// send packet over IBC
		err := ccv.SendIBCPacket(
			ctx,
			k.scopedKeeper,
			k.channelKeeper,
			channelID,          // source channel id
			ccv.ProviderPortID, // source port id
			data.GetBytes(),
			k.GetCCVTimeoutPeriod(ctx),
		)
		if err != nil {
			if errors.Is(err, clienttypes.ErrClientNotActive) {
				// IBC client is expired!
				// leave the packet data stored to be sent once the client is upgraded
				// the client cannot expire during iteration (in the middle of a block)
				k.Logger(ctx).Info("IBC client is expired, cannot send VSC, leaving packet data stored:", "consumerId", chainID, "vscid", data.ValsetUpdateId)
				return
			}
			// Not able to send packet over IBC!
			k.Logger(ctx).Error("cannot send VSC, removing consumer:", "consumerId", chainID, "vscid", data.ValsetUpdateId, "err", err.Error())
			// If this happens, most likely the consumer is malicious; remove it
			err := k.StopConsumerChain(ctx, chainID, true)
			if err != nil {
				panic(fmt.Errorf("consumer chain failed to stop: %w", err))
			}
			return
		}
	}
	k.DeletePendingVSCPackets(ctx, chainID)
}

// QueueVSCPackets queues latest validator updates for every registered consumer chain
// failing to GetLastBondedValidators will cause a panic in EndBlock

// TODO: decide if this func shouldn't return an error to be propagated to BeginBlocker
func (k Keeper) QueueVSCPackets(ctx sdk.Context) {
	valUpdateID := k.GetValidatorSetUpdateId(ctx) // current valset update ID

	// get the bonded validators from the staking module
	bondedValidators, err := k.GetLastBondedValidators(ctx)
	if err != nil {
		panic(fmt.Errorf("failed to get last validators: %w", err))
	}

	for _, chainID := range k.GetAllRegisteredConsumerIds(ctx) {
		currentValidators, err := k.GetConsumerValSet(ctx, chainID)
		if err != nil {
			panic(fmt.Errorf("failed to get consumer validators: %w", err))
		}
		topN := k.GetTopN(ctx, chainID)

		if topN > 0 {
			// in a Top-N chain, we automatically opt in all validators that belong to the top N
			// of the active validators
			activeValidators, err := k.GetLastProviderConsensusActiveValidators(ctx)
			if err != nil {
				// something must be broken in the bonded validators, so we have to panic since there is no realistic way to proceed
				panic(fmt.Errorf("failed to get active validators: %w", err))
			}

			minPower, err := k.ComputeMinPowerInTopN(ctx, activeValidators, topN)
			if err != nil {
				// we panic, since the only way to proceed would be to opt in all validators, which is not the intended behavior
				panic(fmt.Errorf("failed to compute min power to opt in for chain %v: %w", chainID, err))
			}

			// set the minimal power of validators in the top N in the store
			k.SetMinimumPowerInTopN(ctx, chainID, minPower)

			k.OptInTopNValidators(ctx, chainID, activeValidators, minPower)
		}

		nextValidators := k.ComputeNextValidators(ctx, chainID, bondedValidators)

		valUpdates := DiffValidators(currentValidators, nextValidators)
		k.SetConsumerValSet(ctx, chainID, nextValidators)

		// check whether there are changes in the validator set
		if len(valUpdates) != 0 {
			// construct validator set change packet data
			packet := ccv.NewValidatorSetChangePacketData(valUpdates, valUpdateID, k.ConsumeSlashAcks(ctx, chainID))
			k.AppendPendingVSCPackets(ctx, chainID, packet)
			k.Logger(ctx).Info("VSCPacket enqueued:",
				"consumerId", chainID,
				"vscID", valUpdateID,
				"len updates", len(valUpdates),
			)
		}
	}

	k.IncrementValidatorSetUpdateId(ctx)
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
	for _, chainID := range k.GetAllRegisteredConsumerIds(ctx) {
		k.PruneKeyAssignments(ctx, chainID)
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
	chainID, found := k.GetChannelIdToConsumerId(ctx, packet.DestinationChannel)
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

	if err := k.ValidateSlashPacket(ctx, chainID, packet, data); err != nil {
		k.Logger(ctx).Error("invalid slash packet",
			"error", err.Error(),
			"consumerId", chainID,
			"consumer cons addr", sdk.ConsAddress(data.Validator.Address).String(),
			"vscID", data.ValsetUpdateId,
			"infractionType", data.Infraction,
		)
		return nil, err
	}

	// The slash packet validator address may be known only on the consumer chain,
	// in this case, it must be mapped back to the consensus address on the provider chain
	consumerConsAddr := providertypes.NewConsumerConsAddress(data.Validator.Address)
	providerConsAddr := k.GetProviderAddrFromConsumerAddr(ctx, chainID, consumerConsAddr)

	if data.Infraction == stakingtypes.Infraction_INFRACTION_DOUBLE_SIGN {
		// getMappedInfractionHeight is already checked in ValidateSlashPacket
		infractionHeight, _ := k.getMappedInfractionHeight(ctx, chainID, data.ValsetUpdateId)

		k.SetSlashLog(ctx, providerConsAddr)
		k.Logger(ctx).Info("SlashPacket received for double-signing",
			"consumerId", chainID,
			"consumer cons addr", consumerConsAddr.String(),
			"provider cons addr", providerConsAddr.String(),
			"vscID", data.ValsetUpdateId,
			"infractionHeight", infractionHeight,
		)

		// return successful ack, as an error would result
		// in the consumer closing the CCV channel
		return ccv.V1Result, nil
	}

	// Check that the validator belongs to the consumer chain valset
	if !k.IsConsumerValidator(ctx, chainID, providerConsAddr) {
		k.Logger(ctx).Error("cannot jail validator %s that does not belong to consumer %s valset",
			providerConsAddr.String(), chainID)
		// drop packet but return a slash ack so that the consumer can send another slash packet
		k.AppendSlashAck(ctx, chainID, consumerConsAddr.String())

		return ccv.SlashPacketHandledResult, nil
	}

	meter := k.GetSlashMeter(ctx)
	// Return bounce ack if meter is negative in value
	if meter.IsNegative() {
		k.Logger(ctx).Info("SlashPacket received, but meter is negative. Packet will be bounced",
			"consumerId", chainID,
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

	k.HandleSlashPacket(ctx, chainID, data)

	k.Logger(ctx).Info("slash packet received and handled",
		"consumerId", chainID,
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
func (k Keeper) ValidateSlashPacket(ctx sdk.Context, chainID string,
	packet channeltypes.Packet, data ccv.SlashPacketData,
) error {
	_, found := k.getMappedInfractionHeight(ctx, chainID, data.ValsetUpdateId)
	// return error if we cannot find infraction height matching the validator update id
	if !found {
		return fmt.Errorf("cannot find infraction height matching "+
			"the validator update id %d for chain %s", data.ValsetUpdateId, chainID)
	}

	return nil
}

// HandleSlashPacket potentially jails a misbehaving validator for a downtime infraction.
// This method should NEVER be called with a double-sign infraction.
func (k Keeper) HandleSlashPacket(ctx sdk.Context, chainID string, data ccv.SlashPacketData) {
	consumerConsAddr := providertypes.NewConsumerConsAddress(data.Validator.Address)
	// Obtain provider chain consensus address using the consumer chain consensus address
	providerConsAddr := k.GetProviderAddrFromConsumerAddr(ctx, chainID, consumerConsAddr)

	k.Logger(ctx).Debug("HandleSlashPacket",
		"consumerId", chainID,
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

	infractionHeight, found := k.getMappedInfractionHeight(ctx, chainID, data.ValsetUpdateId)
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

	// append the validator address to the slash ack for its chain id
	// TODO: consumer cons address should be accepted here
	k.AppendSlashAck(ctx, chainID, consumerConsAddr.String())

	// jail validator
	if !validator.IsJailed() {
		err := k.stakingKeeper.Jail(ctx, providerConsAddr.ToSdkConsAddr())
		if err != nil {
			k.Logger(ctx).Error("failed to jail vaidator", providerConsAddr.ToSdkConsAddr().String(), "err", err.Error())
			return
		}
		k.Logger(ctx).Info("HandleSlashPacket - validator jailed", "provider cons addr", providerConsAddr.String())
		jailDuration, err := k.slashingKeeper.DowntimeJailDuration(ctx)
		if err != nil {
			k.Logger(ctx).Error("failed to get jail duration", "err", err.Error())
			return
		}
		jailEndTime := ctx.BlockTime().Add(jailDuration)
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

// getMappedInfractionHeight gets the infraction height mapped from val set ID for the given chain ID
func (k Keeper) getMappedInfractionHeight(ctx sdk.Context,
	chainID string, valsetUpdateID uint64,
) (height uint64, found bool) {
	if valsetUpdateID == 0 {
		return k.GetInitChainHeight(ctx, chainID)
	} else {
		return k.GetValsetUpdateBlockHeight(ctx, valsetUpdateID)
	}
}
