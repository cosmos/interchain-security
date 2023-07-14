package keeper

import (
	"fmt"
	"strconv"

	clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v7/modules/core/04-channel/types"
	"github.com/cosmos/ibc-go/v7/modules/core/exported"

	errorsmod "cosmossdk.io/errors"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	abci "github.com/cometbft/cometbft/abci/types"

	"github.com/cosmos/interchain-security/v3/x/ccv/consumer/types"
	ccv "github.com/cosmos/interchain-security/v3/x/ccv/types"
)

// OnRecvVSCPacket sets the pending validator set changes that will be flushed to ABCI on Endblock
// and set the maturity time for the packet. Once the maturity time elapses, a VSCMatured packet is
// sent back to the provider chain.
//
// Note: CCV uses an ordered IBC channel, meaning VSC packet changes will be accumulated (and later
// processed by ApplyCCValidatorChanges) s.t. more recent val power changes overwrite older ones.
func (k Keeper) OnRecvVSCPacket(ctx sdk.Context, packet channeltypes.Packet, newChanges ccv.ValidatorSetChangePacketData) exported.Acknowledgement {
	// get the provider channel
	providerChannel, found := k.GetProviderChannel(ctx)
	if found && providerChannel != packet.DestinationChannel {
		// VSC packet was sent on a channel different than the provider channel;
		// this should never happen
		panic(fmt.Errorf("VSCPacket received on unknown channel %s; expected: %s",
			packet.DestinationChannel, providerChannel))
	}
	if !found {
		// the first packet from the provider chain
		// - mark the CCV channel as established
		k.SetProviderChannel(ctx, packet.DestinationChannel)
		k.Logger(ctx).Info("CCV channel established", "port", packet.DestinationPort, "channel", packet.DestinationChannel)

		// emit event on first VSC packet to signal that CCV is working
		ctx.EventManager().EmitEvent(
			sdk.NewEvent(
				ccv.EventTypeChannelEstablished,
				sdk.NewAttribute(sdk.AttributeKeyModule, types.ModuleName),
				sdk.NewAttribute(channeltypes.AttributeKeyChannelID, packet.DestinationChannel),
				sdk.NewAttribute(channeltypes.AttributeKeyPortID, packet.DestinationPort),
			),
		)
	}
	// Set pending changes by accumulating changes from this packet with all prior changes
	currentValUpdates := []abci.ValidatorUpdate{}
	currentChanges, exists := k.GetPendingChanges(ctx)
	if exists {
		currentValUpdates = currentChanges.ValidatorUpdates
	}
	pendingChanges := ccv.AccumulateChanges(currentValUpdates, newChanges.ValidatorUpdates)

	k.SetPendingChanges(ctx, ccv.ValidatorSetChangePacketData{
		ValidatorUpdates: pendingChanges,
	})

	// Save maturity time and packet
	maturityTime := ctx.BlockTime().Add(k.GetUnbondingPeriod(ctx))
	k.SetPacketMaturityTime(ctx, newChanges.ValsetUpdateId, maturityTime)
	k.Logger(ctx).Debug("packet maturity time was set",
		"vscID", newChanges.ValsetUpdateId,
		"maturity time (utc)", maturityTime.UTC(),
		"maturity time (nano)", uint64(maturityTime.UnixNano()),
	)

	// set height to VSC id mapping
	blockHeight := uint64(ctx.BlockHeight()) + 1
	k.SetHeightValsetUpdateID(ctx, blockHeight, newChanges.ValsetUpdateId)
	k.Logger(ctx).Debug("block height was mapped to vscID", "height", blockHeight, "vscID", newChanges.ValsetUpdateId)

	// remove outstanding slashing flags of the validators
	// for which the slashing was acknowledged by the provider chain
	for _, addr := range newChanges.GetSlashAcks() {
		k.DeleteOutstandingDowntime(ctx, addr)
	}

	k.Logger(ctx).Info("finished receiving/handling VSCPacket",
		"vscID", newChanges.ValsetUpdateId,
		"len updates", len(newChanges.ValidatorUpdates),
		"len slash acks", len(newChanges.SlashAcks),
	)
	ack := channeltypes.NewResultAcknowledgement([]byte{byte(1)})
	return ack
}

// QueueVSCMaturedPackets appends matured VSCs to an internal queue.
//
// Note: Per spec, a VSC reaching maturity on a consumer chain means that all the unbonding
// operations that resulted in validator updates included in that VSC have matured on
// the consumer chain.
func (k Keeper) QueueVSCMaturedPackets(ctx sdk.Context) {
	for _, maturityTime := range k.GetElapsedPacketMaturityTimes(ctx) {
		// construct validator set change packet data
		vscPacket := ccv.NewVSCMaturedPacketData(maturityTime.VscId)

		// Append VSCMatured packet to pending packets.
		// Sending packets is attempted each EndBlock.
		// Unsent packets remain in the queue until sent.
		k.AppendPendingPacket(ctx,
			ccv.VscMaturedPacket,
			&ccv.ConsumerPacketData_VscMaturedPacketData{VscMaturedPacketData: vscPacket},
		)

		k.DeletePacketMaturityTimes(ctx, maturityTime.VscId, maturityTime.MaturityTime)

		k.Logger(ctx).Info("VSCMaturedPacket enqueued", "vscID", vscPacket.ValsetUpdateId)

		ctx.EventManager().EmitEvent(
			sdk.NewEvent(
				ccv.EventTypeVSCMatured,
				sdk.NewAttribute(sdk.AttributeKeyModule, types.ModuleName),
				sdk.NewAttribute(ccv.AttributeChainID, ctx.ChainID()),
				sdk.NewAttribute(ccv.AttributeConsumerHeight, strconv.Itoa(int(ctx.BlockHeight()))),
				sdk.NewAttribute(ccv.AttributeValSetUpdateID, strconv.Itoa(int(maturityTime.VscId))),
				sdk.NewAttribute(ccv.AttributeTimestamp, ctx.BlockTime().String()),
			),
		)
	}
}

// QueueSlashPacket appends a slash packet containing the given validator data and slashing info to queue.
func (k Keeper) QueueSlashPacket(ctx sdk.Context, validator abci.Validator, valsetUpdateID uint64, infraction stakingtypes.Infraction) {
	consAddr := sdk.ConsAddress(validator.Address)
	downtime := infraction == stakingtypes.Infraction_INFRACTION_DOWNTIME

	// return if an outstanding downtime request is set for the validator
	if downtime && k.OutstandingDowntime(ctx, consAddr) {
		return
	}

	if downtime {
		// set outstanding downtime to not send multiple
		// slashing requests for the same downtime infraction
		k.SetOutstandingDowntime(ctx, consAddr)
	}

	// construct slash packet data
	slashPacket := ccv.NewSlashPacketData(validator, valsetUpdateID, infraction)

	// append the Slash packet data to pending data packets
	// to be sent once the CCV channel is established
	k.AppendPendingPacket(ctx,
		ccv.SlashPacket,
		&ccv.ConsumerPacketData_SlashPacketData{
			SlashPacketData: slashPacket,
		},
	)

	k.Logger(ctx).Info("SlashPacket enqueued",
		"vscID", slashPacket.ValsetUpdateId,
		"validator cons addr", sdk.ConsAddress(slashPacket.Validator.Address).String(),
		"infraction", slashPacket.Infraction,
	)

	ctx.EventManager().EmitEvent(
		sdk.NewEvent(
			ccv.EventTypeConsumerSlashRequest,
			sdk.NewAttribute(sdk.AttributeKeyModule, types.ModuleName),
			sdk.NewAttribute(ccv.AttributeValidatorAddress, sdk.ConsAddress(validator.Address).String()),
			sdk.NewAttribute(ccv.AttributeValSetUpdateID, strconv.Itoa(int(valsetUpdateID))),
			sdk.NewAttribute(ccv.AttributeInfractionType, infraction.String()),
		),
	)
}

// SendPackets iterates queued packets and sends them in FIFO order.
// received VSC packets in order, and write acknowledgements for all matured VSC packets.
//
// This method is a no-op if there is no established channel to provider or the queue is empty.
//
// Note: Per spec, a VSC reaching maturity on a consumer chain means that all the unbonding
// operations that resulted in validator updates included in that VSC have matured on
// the consumer chain.
func (k Keeper) SendPackets(ctx sdk.Context) {
	channelID, ok := k.GetProviderChannel(ctx)
	if !ok {
		return
	}

	pending := k.GetPendingPackets(ctx)
	idxsForDeletion := []uint64{}
	for _, p := range pending {
		if !k.PacketSendingPermitted(ctx) {
			return
		}

		// Send packet over IBC
		err := ccv.SendIBCPacket(
			ctx,
			k.scopedKeeper,
			k.channelKeeper,
			channelID,          // source channel id
			ccv.ConsumerPortID, // source port id
			p.GetBytes(),
			k.GetCCVTimeoutPeriod(ctx),
		)
		if err != nil {
			if clienttypes.ErrClientNotActive.Is(err) {
				// IBC client is expired!
				// leave the packet data stored to be sent once the client is upgraded
				k.Logger(ctx).Info("IBC client is expired, cannot send IBC packet; leaving packet data stored:", "type", p.Type.String())
				break
			}
			// Not able to send packet over IBC!
			// Leave the packet data stored for the sent to be retried in the next block.
			// Note that if VSCMaturedPackets are not sent for long enough, the provider
			// will remove the consumer anyway.
			k.Logger(ctx).Error("cannot send IBC packet; leaving packet data stored:", "type", p.Type.String(), "err", err.Error())
			break
		}
		// If the packet that was just sent was a Slash packet, set the waiting on slash reply flag.
		// This flag will be toggled false again when consumer hears back from provider. See OnAcknowledgementPacket below.
		if p.Type == ccv.SlashPacket {
			k.UpdateSlashRecordOnSend(ctx)
			// Break so slash stays at head of queue
			break
		} else {
			// Otherwise the vsc matured will be deleted
			idxsForDeletion = append(idxsForDeletion, p.Idx)
		}
	}
	// Delete pending packets that were successfully sent and did not return an error from SendIBCPacket
	k.DeletePendingDataPackets(ctx, idxsForDeletion...)
}

// OnAcknowledgementPacket executes application logic for acknowledgments of sent VSCMatured and Slash packets
// in conjunction with the ibc module's execution of "acknowledgePacket",
// according to https://github.com/cosmos/ibc/tree/main/spec/core/ics-004-channel-and-packet-semantics#processing-acknowledgements
func (k Keeper) OnAcknowledgementPacket(ctx sdk.Context, packet channeltypes.Packet, ack channeltypes.Acknowledgement) error {
	if res := ack.GetResult(); res != nil {
		if len(res) != 1 {
			k.Logger(ctx).Error("recv invalid ack; expected length 1", "channel", packet.SourceChannel, "ack", res)
		}

		// Unmarshal into V1 consumer packet data type. We trust data is formed correctly
		// as it was originally marshalled by this module, and consumers must trust the provider
		// did not tamper with the data. Note ConsumerPacketData.GetBytes() always JSON marshals to the
		// ConsumerPacketDataV1 type which is sent over the wire.
		var consumerPacket ccv.ConsumerPacketDataV1
		ccv.ModuleCdc.MustUnmarshalJSON(packet.GetData(), &consumerPacket)
		// If this ack is regarding a provider handling a vsc matured packet, there's nothing to do.
		// As vsc matured packets are popped from the consumer pending packets queue on send.
		if consumerPacket.Type == ccv.VscMaturedPacket {
			return nil
		}

		// Otherwise we handle the result of the slash packet acknowledgement.
		switch res[0] {
		// We treat a v1 result as the provider successfully queuing the slash packet w/o need for retry.
		case ccv.V1Result[0]:
			k.ClearSlashRecord(ctx)           // Clears slash record state, unblocks sending of pending packets.
			k.DeleteHeadOfPendingPackets(ctx) // Remove slash from head of queue. It's been handled.
		case ccv.SlashPacketHandledResult[0]:
			k.ClearSlashRecord(ctx)           // Clears slash record state, unblocks sending of pending packets.
			k.DeleteHeadOfPendingPackets(ctx) // Remove slash from head of queue. It's been handled.
		case ccv.SlashPacketBouncedResult[0]:
			k.UpdateSlashRecordOnBounce(ctx)
			// Note slash is still at head of queue and will now be retried after appropriate delay period.
		default:
			k.Logger(ctx).Error("recv invalid result ack; expected 1, 2, or 3", "channel", packet.SourceChannel, "ack", res)
		}
	}

	if err := ack.GetError(); err != "" {
		// Reasons for ErrorAcknowledgment
		//  - packet data could not be successfully decoded
		//  - invalid Slash packet
		// None of these should ever happen.
		k.Logger(ctx).Error(
			"recv ErrorAcknowledgement",
			"channel", packet.SourceChannel,
			"error", err,
		)
		// Initiate ChanCloseInit using packet source (non-counterparty) port and channel
		err := k.ChanCloseInit(ctx, packet.SourcePort, packet.SourceChannel)
		if err != nil {
			return fmt.Errorf("ChanCloseInit(%s) failed: %s", packet.SourceChannel, err.Error())
		}
		// check if there is an established CCV channel to provider
		channelID, found := k.GetProviderChannel(ctx)
		if !found {
			return errorsmod.Wrapf(types.ErrNoProposerChannelId, "recv ErrorAcknowledgement on non-established channel %s", packet.SourceChannel)
		}
		if channelID != packet.SourceChannel {
			// Close the established CCV channel as well
			return k.ChanCloseInit(ctx, ccv.ConsumerPortID, channelID)
		}
	}
	return nil
}

// IsChannelClosed returns a boolean whether a given channel is in the CLOSED state
func (k Keeper) IsChannelClosed(ctx sdk.Context, channelID string) bool {
	channel, found := k.channelKeeper.GetChannel(ctx, ccv.ConsumerPortID, channelID)
	if !found || channel.State == channeltypes.CLOSED {
		return true
	}
	return false
}
