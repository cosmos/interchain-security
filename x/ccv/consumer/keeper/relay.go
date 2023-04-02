package keeper

import (
	"fmt"
	"sort"
	"strconv"
	"time"

	abci "github.com/cometbft/cometbft/abci/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v7/modules/core/04-channel/types"
	host "github.com/cosmos/ibc-go/v7/modules/core/24-host"
	"github.com/cosmos/ibc-go/v7/modules/core/exported"
	"github.com/cosmos/interchain-security/x/consumer/types"
	consumertypes "github.com/cosmos/interchain-security/x/consumer/types"
)

// OnRecvVSCPacket sets the pending validator set changes that will be flushed to ABCI on Endblock
// and set the maturity time for the packet. Once the maturity time elapses, a VSCMatured packet is
// sent back to the provider chain.
//
// Note: CCV uses an ordered IBC channel, meaning VSC packet changes will be accumulated (and later
// processed by ApplyCCValidatorChanges) s.t. more recent val power changes overwrite older ones.
func (k Keeper) OnRecvVSCPacket(ctx sdk.Context, packet channeltypes.Packet, newChanges consumertypes.ValidatorSetChangePacketData) exported.Acknowledgement {
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
				consumertypes.EventTypeChannelEstablished,
				sdk.NewAttribute(sdk.AttributeKeyModule, types.ModuleName),
				sdk.NewAttribute(channeltypes.AttributeKeyChannelID, packet.DestinationChannel),
				sdk.NewAttribute(channeltypes.AttributeKeyPortID, packet.DestinationPort),
			),
		)
	}
	// Set pending changes by accumulating changes from this packet with all prior changes
	var pendingChanges []abci.ValidatorUpdate
	currentChanges, exists := k.GetPendingChanges(ctx)
	if !exists {
		pendingChanges = newChanges.ValidatorUpdates
	} else {
		pendingChanges = AccumulateChanges(currentChanges.ValidatorUpdates, newChanges.ValidatorUpdates)
	}

	k.SetPendingChanges(ctx, consumertypes.ValidatorSetChangePacketData{
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
		vscPacket := consumertypes.NewVSCMaturedPacketData(maturityTime.VscId)

		// Append VSCMatured packet to pending packets.
		// Sending packets is attempted each EndBlock.
		// Unsent packets remain in the queue until sent.
		k.AppendPendingPacket(ctx, consumertypes.ConsumerPacketData{
			Type: consumertypes.VscMaturedPacket,
			Data: &consumertypes.ConsumerPacketData_VscMaturedPacketData{VscMaturedPacketData: vscPacket},
		})

		k.DeletePacketMaturityTimes(ctx, maturityTime.VscId, maturityTime.MaturityTime)

		k.Logger(ctx).Info("VSCMaturedPacket enqueued", "vscID", vscPacket.ValsetUpdateId)

		ctx.EventManager().EmitEvent(
			sdk.NewEvent(
				consumertypes.EventTypeVSCMatured,
				sdk.NewAttribute(sdk.AttributeKeyModule, types.ModuleName),
				sdk.NewAttribute(consumertypes.AttributeChainID, ctx.ChainID()),
				sdk.NewAttribute(consumertypes.AttributeConsumerHeight, strconv.Itoa(int(ctx.BlockHeight()))),
				sdk.NewAttribute(consumertypes.AttributeValSetUpdateID, strconv.Itoa(int(maturityTime.VscId))),
				sdk.NewAttribute(consumertypes.AttributeTimestamp, ctx.BlockTime().String()),
			),
		)
	}
}

// QueueSlashPacket appends a slash packet containing the given validator data and slashing info to queue.
func (k Keeper) QueueSlashPacket(ctx sdk.Context, validator abci.Validator, valsetUpdateID uint64, infraction stakingtypes.Infraction) {
	consAddr := sdk.ConsAddress(validator.Address)
	downtime := infraction == stakingtypes.Downtime

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
	slashPacket := consumertypes.NewSlashPacketData(validator, valsetUpdateID, infraction)

	// append the Slash packet data to pending data packets
	// to be sent once the CCV channel is established
	k.AppendPendingPacket(ctx, consumertypes.ConsumerPacketData{
		Type: consumertypes.SlashPacket,
		Data: &consumertypes.ConsumerPacketData_SlashPacketData{
			SlashPacketData: slashPacket,
		},
	})

	k.Logger(ctx).Info("SlashPacket enqueued",
		"vscID", slashPacket.ValsetUpdateId,
		"validator cons addr", sdk.ConsAddress(slashPacket.Validator.Address).String(),
		"infraction", slashPacket.Infraction,
	)

	ctx.EventManager().EmitEvent(
		sdk.NewEvent(
			consumertypes.EventTypeConsumerSlashRequest,
			sdk.NewAttribute(sdk.AttributeKeyModule, types.ModuleName),
			sdk.NewAttribute(consumertypes.AttributeValidatorAddress, sdk.ConsAddress(validator.Address).String()),
			sdk.NewAttribute(consumertypes.AttributeValSetUpdateID, strconv.Itoa(int(valsetUpdateID))),
			sdk.NewAttribute(consumertypes.AttributeInfractionType, infraction.String()),
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
	for _, p := range pending.GetList() {

		// send packet over IBC
		err := SendIBCPacket(
			ctx,
			k.scopedKeeper,
			k.channelKeeper,
			channelID,                    // source channel id
			consumertypes.ConsumerPortID, // source port id
			p.GetBytes(),
			k.GetCCVTimeoutPeriod(ctx),
		)
		if err != nil {
			if clienttypes.ErrClientNotActive.Is(err) {
				k.Logger(ctx).Debug("IBC client is inactive, packet remains in queue", "type", p.Type.String())
				// leave the packet data stored to be sent once the client is upgraded
				return
			}
			// something went wrong when sending the packet
			// TODO do not panic if the send fails
			panic(fmt.Errorf("packet could not be sent over IBC: %w", err))
		}
	}

	// clear pending data packets
	k.DeletePendingDataPackets(ctx)
}

// OnAcknowledgementPacket executes application logic for acknowledgments of sent VSCMatured and Slash packets
// in conjunction with the ibc module's execution of "acknowledgePacket",
// according to https://github.com/cosmos/ibc/tree/main/spec/core/ics-004-channel-and-packet-semantics#processing-acknowledgements
func (k Keeper) OnAcknowledgementPacket(ctx sdk.Context, packet channeltypes.Packet, ack channeltypes.Acknowledgement) error {
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
			return sdkerrors.Wrapf(types.ErrNoProposerChannelId, "recv ErrorAcknowledgement on non-established channel %s", packet.SourceChannel)
		}
		if channelID != packet.SourceChannel {
			// Close the established CCV channel as well
			return k.ChanCloseInit(ctx, consumertypes.ConsumerPortID, channelID)
		}
	}
	return nil
}

// IsChannelClosed returns a boolean whether a given channel is in the CLOSED state
func (k Keeper) IsChannelClosed(ctx sdk.Context, channelID string) bool {
	channel, found := k.channelKeeper.GetChannel(ctx, consumertypes.ConsumerPortID, channelID)
	if !found || channel.State == channeltypes.CLOSED {
		return true
	}
	return false
}

// SendIBCPacket sends an IBC packet with packetData
// over the source channelID and portID
func SendIBCPacket(
	ctx sdk.Context,
	scopedKeeper consumertypes.ScopedKeeper,
	channelKeeper consumertypes.ChannelKeeper,
	channelID string,
	portID string,
	packetData []byte,
	timeoutPeriod time.Duration,
) error {
	channel, ok := channelKeeper.GetChannel(ctx, portID, channelID)
	if !ok {
		return sdkerrors.Wrapf(channeltypes.ErrChannelNotFound, "channel not found for channel ID: %s", channelID)
	}
	channelCap, ok := scopedKeeper.GetCapability(ctx, host.ChannelCapabilityPath(portID, channelID))
	if !ok {
		return sdkerrors.Wrap(channeltypes.ErrChannelCapabilityNotFound, "module does not own channel capability")
	}

	// get the next sequence
	sequence, found := channelKeeper.GetNextSequenceSend(ctx, portID, channelID)
	if !found {
		return sdkerrors.Wrapf(
			channeltypes.ErrSequenceSendNotFound,
			"source port: %s, source channel: %s", portID, channelID,
		)
	}
	packet := channeltypes.NewPacket(
		packetData, sequence,
		portID, channelID,
		channel.Counterparty.PortId, channel.Counterparty.ChannelId,
		clienttypes.Height{}, uint64(ctx.BlockTime().Add(timeoutPeriod).UnixNano()),
	)

	return channelKeeper.SendPacket(ctx, channelCap, packet)
}

// keep
func AccumulateChanges(currentChanges, newChanges []abci.ValidatorUpdate) []abci.ValidatorUpdate {
	m := make(map[string]abci.ValidatorUpdate)

	for i := 0; i < len(currentChanges); i++ {
		m[currentChanges[i].PubKey.String()] = currentChanges[i]
	}

	for i := 0; i < len(newChanges); i++ {
		m[newChanges[i].PubKey.String()] = newChanges[i]
	}

	var out []abci.ValidatorUpdate

	for _, update := range m {
		out = append(out, update)
	}

	// The list of tendermint updates should hash the same across all consensus nodes
	// that means it is necessary to sort for determinism.
	sort.Slice(out, func(i, j int) bool {
		if out[i].Power != out[j].Power {
			return out[i].Power > out[j].Power
		}
		return out[i].PubKey.String() > out[j].PubKey.String()
	})

	return out
}
