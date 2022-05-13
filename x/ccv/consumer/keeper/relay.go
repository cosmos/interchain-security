package keeper

import (
	"encoding/binary"
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	host "github.com/cosmos/ibc-go/v3/modules/core/24-host"
	"github.com/cosmos/ibc-go/v3/modules/core/exported"
	"github.com/cosmos/interchain-security/x/ccv/consumer/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	utils "github.com/cosmos/interchain-security/x/ccv/utils"
	abci "github.com/tendermint/tendermint/abci/types"
)

// OnRecvPacket sets the pending validator set changes that will be flushed to ABCI on Endblock
// and set the unbonding time for the packet so that we can WriteAcknowledgement after unbonding time is over.
func (k Keeper) OnRecvPacket(ctx sdk.Context, packet channeltypes.Packet, newChanges ccv.ValidatorSetChangePacketData) exported.Acknowledgement {
	// packet is not sent on provider channel, return error acknowledgement and close channel
	if providerChannel, ok := k.GetProviderChannel(ctx); ok && providerChannel != packet.DestinationChannel {
		ack := channeltypes.NewErrorAcknowledgement(
			fmt.Sprintf("packet sent on a channel %s other than the established provider channel %s", packet.DestinationChannel, providerChannel),
		)
		chanCap, _ := k.scopedKeeper.GetCapability(ctx, host.ChannelCapabilityPath(packet.DestinationPort, packet.DestinationChannel))
		k.channelKeeper.ChanCloseInit(ctx, packet.DestinationPort, packet.DestinationChannel, chanCap)
		return &ack
	}
	if status := k.GetChannelStatus(ctx, packet.DestinationChannel); status != ccv.VALIDATING {
		// Set CCV channel status to Validating and set provider channel
		k.SetChannelStatus(ctx, packet.DestinationChannel, ccv.VALIDATING)
		k.SetProviderChannel(ctx, packet.DestinationChannel)
		// Send pending slash requests in states
		k.SendPendingSlashRequests(ctx)
	}
	// Set pending changes by accumulating changes from this packet with all prior changes
	var pendingChanges []abci.ValidatorUpdate
	currentChanges, exists := k.GetPendingChanges(ctx)
	if !exists {
		pendingChanges = newChanges.ValidatorUpdates
	} else {
		pendingChanges = utils.AccumulateChanges(currentChanges.ValidatorUpdates, newChanges.ValidatorUpdates)
	}
	k.SetPendingChanges(ctx, ccv.ValidatorSetChangePacketData{
		ValidatorUpdates: pendingChanges,
	})

	// Save unbonding time and packet
	unbondingTime := ctx.BlockTime().Add(types.UnbondingTime)
	k.SetUnbondingTime(ctx, packet.Sequence, uint64(unbondingTime.UnixNano()))
	k.SetUnbondingPacket(ctx, packet.Sequence, packet)

	// set height to VSC id mapping
	k.SetHeightValsetUpdateID(ctx, uint64(ctx.BlockHeight())+1, newChanges.ValsetUpdateId)

	// set outstanding slashing flags to false
	for _, addr := range newChanges.GetSlashAcks() {
		k.ClearOutstandingDowntime(ctx, addr)
	}

	// ack will be sent asynchronously
	return nil
}

// UnbondMaturePackets will iterate over the unbonding packets in order and write acknowledgements for all
// packets that have finished unbonding.
func (k Keeper) UnbondMaturePackets(ctx sdk.Context) error {
	store := ctx.KVStore(k.storeKey)
	unbondingIterator := sdk.KVStorePrefixIterator(store, []byte(types.UnbondingTimePrefix))
	defer unbondingIterator.Close()

	currentTime := uint64(ctx.BlockTime().UnixNano())

	channelID, ok := k.GetProviderChannel(ctx)
	if !ok {
		return sdkerrors.Wrap(channeltypes.ErrChannelNotFound, "provider channel not set")
	}
	channelCap, ok := k.scopedKeeper.GetCapability(ctx, host.ChannelCapabilityPath(types.PortID, channelID))
	if !ok {
		return sdkerrors.Wrap(channeltypes.ErrChannelCapabilityNotFound, "module does not own channel capability")
	}

	for unbondingIterator.Valid() {
		sequence := types.GetSequenceFromUnbondingTimeKey(unbondingIterator.Key())
		if currentTime > binary.BigEndian.Uint64(unbondingIterator.Value()) {
			// write successful ack and delete unbonding information
			packet, err := k.GetUnbondingPacket(ctx, sequence)
			if err != nil {
				return err
			}
			ack := channeltypes.NewResultAcknowledgement([]byte{byte(1)})
			k.channelKeeper.WriteAcknowledgement(ctx, channelCap, packet, ack)
			k.DeleteUnbondingTime(ctx, sequence)
			k.DeleteUnbondingPacket(ctx, sequence)
		} else {
			break
		}
		unbondingIterator.Next()
	}
	return nil
}

// SendSlashPacket sends a slash packet containing the given validator data and slashing info
func (k Keeper) SendSlashPacket(ctx sdk.Context, validator abci.Validator, valsetUpdateID uint64, infraction stakingtypes.InfractionType) {
	consAddr := sdk.ConsAddress(validator.Address)
	downtime := infraction == stakingtypes.Downtime

	// return if an outstanding downtime request is set for the validator
	if downtime && k.OutstandingDowntime(ctx, consAddr) {
		return
	}

	// construct slash packet data
	packetData := ccv.NewSlashPacketData(validator, valsetUpdateID, infraction)

	// check that provider channel is established
	// if not, append slashing packet to pending slash requests
	channelID, ok := k.GetProviderChannel(ctx)
	if !ok {
		k.AppendPendingSlashRequests(ctx, types.SlashRequest{
			Packet:   &packetData,
			Downtime: downtime},
		)
		return
	}

	// send packet over IBC
	err := utils.SendIBCPacket(
		ctx,
		k.scopedKeeper,
		k.channelKeeper,
		channelID,    // source channel id
		types.PortID, // source port id
		packetData.GetBytes(),
	)
	if err != nil {
		panic(err)
	}

	// set outstanding downtime if slash request sent is for downtime
	if downtime {
		k.SetOutstandingDowntime(ctx, consAddr)
	}
}

// SendPendingSlashRequests iterates over the stored pending slash requests in reverse order
// and sends the embedded slash packets to the provider chain
func (k Keeper) SendPendingSlashRequests(ctx sdk.Context) {
	channelID, ok := k.GetProviderChannel(ctx)
	if !ok {
		panic(fmt.Errorf("%s: CCV channel not set", channeltypes.ErrChannelNotFound))
	}

	// iterate over pending slash requests in reverse order
	requests := k.GetPendingSlashRequests(ctx)
	for i := len(requests) - 1; i >= 0; i-- {
		slashReq := requests[i]

		// send the emebdded slash packet to the CCV channel
		// if the outstanding downtime flag is false for the validator
		if !slashReq.Downtime || !k.OutstandingDowntime(ctx, sdk.ConsAddress(slashReq.Packet.Validator.Address)) {
			// send packet over IBC
			err := utils.SendIBCPacket(
				ctx,
				k.scopedKeeper,
				k.channelKeeper,
				channelID,    // source channel id
				types.PortID, // source port id
				requests[i].Packet.GetBytes(),
			)
			if err != nil {
				panic(err)
			}

			// set validator outstanding downtime flag to true
			if slashReq.Downtime {
				k.SetOutstandingDowntime(ctx, sdk.ConsAddress(slashReq.Packet.Validator.Address))
			}
		}
	}

	// clear pending slash requests
	k.ClearPendingSlashRequests(ctx)
}

func (k Keeper) OnAcknowledgementPacket(ctx sdk.Context, packet channeltypes.Packet, data ccv.SlashPacketData, ack channeltypes.Acknowledgement) error {
	if err := ack.GetError(); err != "" {
		// slashing packet was sent to a nonestablished channel
		if err != sdkerrors.Wrap(
			channeltypes.ErrInvalidChannelState,
			packet.DestinationChannel,
		).Error() {
			return fmt.Errorf(err)
		}
	}

	return nil
}

func (k Keeper) OnTimeoutPacket(ctx sdk.Context, packet channeltypes.Packet, data ccv.SlashPacketData) error {
	k.SetChannelStatus(ctx, packet.DestinationChannel, ccv.INVALID)
	return nil
}
