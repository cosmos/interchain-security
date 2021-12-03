package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	clienttypes "github.com/cosmos/ibc-go/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/modules/core/04-channel/types"
	host "github.com/cosmos/ibc-go/modules/core/24-host"
	"github.com/cosmos/interchain-security/x/ccv/parent/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	abci "github.com/tendermint/tendermint/abci/types"
)

func (k Keeper) SendPacket(ctx sdk.Context, chainID string, valUpdates []abci.ValidatorUpdate, valUpdateID uint64) error {
	packetData := ccv.NewValidatorSetChangePacketData(valUpdates, valUpdateID)
	packetDataBytes := packetData.GetBytes()

	channelID, ok := k.GetChainToChannel(ctx, chainID)
	if !ok {
		return sdkerrors.Wrapf(channeltypes.ErrChannelNotFound, "channel not found for channel ID: %s", channelID)
	}
	channel, ok := k.channelKeeper.GetChannel(ctx, types.PortID, channelID)
	if !ok {
		return sdkerrors.Wrapf(channeltypes.ErrChannelNotFound, "channel not found for channel ID: %s", channelID)
	}
	channelCap, ok := k.scopedKeeper.GetCapability(ctx, host.ChannelCapabilityPath(types.PortID, channelID))
	if !ok {
		return sdkerrors.Wrap(channeltypes.ErrChannelCapabilityNotFound, "module does not own channel capability")
	}

	// get the next sequence
	sequence, found := k.channelKeeper.GetNextSequenceSend(ctx, types.PortID, channelID)
	if !found {
		return sdkerrors.Wrapf(
			channeltypes.ErrSequenceSendNotFound,
			"source port: %s, source channel: %s", types.PortID, channelID,
		)
	}

	// Send ValidatorSet changes in IBC packet
	packet := channeltypes.NewPacket(
		packetDataBytes, sequence,
		types.PortID, channelID,
		channel.Counterparty.PortId, channel.Counterparty.ChannelId,
		clienttypes.Height{}, uint64(types.GetTimeoutTimestamp(ctx.BlockTime()).UnixNano()),
	)
	if err := k.channelKeeper.SendPacket(ctx, channelCap, packet); err != nil {
		return err
	}

	return nil
}

func removeStringFromSlice(slice []string, x string) (newSlice []string, numRemoved int) {
	for _, y := range slice {
		if x != y {
			newSlice = append(newSlice, y)
		}
	}

	return newSlice, len(slice) - len(newSlice)
}

func (k Keeper) OnAcknowledgementPacket(ctx sdk.Context, packet channeltypes.Packet, data ccv.ValidatorSetChangePacketData, ack channeltypes.Acknowledgement) error {
	println("+++++  OnAcknowledgementPacket")
	chainID, ok := k.GetChannelToChain(ctx, packet.DestinationChannel)
	if !ok {
		return sdkerrors.Wrapf(ccv.ErrInvalidChildChain, "chain ID doesn't exist for channel ID: %s", packet.DestinationChannel)
	}
	if err := data.Unmarshal(packet.GetData()); err != nil {
		return err
	}

	UBDEs, _ := k.GetUBDEsFromIndex(ctx, chainID, data.ValsetUpdateId)

	for _, UBDE := range UBDEs {
		// remove child chain ID from ubde
		UBDE.UnbondingChildChains, _ = removeStringFromSlice(UBDE.UnbondingChildChains, chainID)

		// If UBDE is completely unbonded from all relevant child chains
		if len(UBDE.UnbondingChildChains) == 0 {
			// Attempt to complete unbonding in staking module
			_, err := k.stakingKeeper.CompleteStoppedUnbonding(ctx, UBDE.UnbondingDelegationEntryId)
			if err != nil {
				return err
			}
			// Delete UBDE
			k.DeleteUnbondingDelegationEntry(ctx, UBDE.UnbondingDelegationEntryId)
		} else {
			k.SetUnbondingDelegationEntry(ctx, UBDE)
		}
	}

	// clean up index
	k.DeleteUBDEIndex(ctx, chainID, data.ValsetUpdateId)

	return nil
}

func (k Keeper) OnTimeoutPacket(ctx sdk.Context, packet channeltypes.Packet, data ccv.ValidatorSetChangePacketData) error {
	k.SetChannelStatus(ctx, packet.DestinationChannel, ccv.INVALID)
	// TODO: Unbonding everything?
	return nil
}

// EndBlockCallback is called for each baby chain in Endblock. It sends latest validator updates to each baby chain
// in a packet over the CCV channel.
func (k Keeper) EndBlockCallback(ctx sdk.Context) {
	valUpdateID := k.GetValidatorSetUpdateId(ctx)
	k.IterateBabyChains(ctx, func(ctx sdk.Context, chainID string) (stop bool) {
		println("iter EndBlockCallback")
		valUpdates := k.stakingKeeper.GetValidatorUpdates(ctx)
		if len(valUpdates) != 0 {
			k.SendPacket(ctx, chainID, valUpdates, valUpdateID)
		}
		return false
	})
	k.IncrementValidatorSetUpdateId(ctx)
}
