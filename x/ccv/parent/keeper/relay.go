package keeper

import (
	"fmt"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	clienttypes "github.com/cosmos/ibc-go/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/modules/core/04-channel/types"
	host "github.com/cosmos/ibc-go/modules/core/24-host"
	"github.com/cosmos/ibc-go/modules/core/exported"
	"github.com/cosmos/interchain-security/x/ccv/parent/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	abci "github.com/tendermint/tendermint/abci/types"
)

func (k Keeper) SendPacket(ctx sdk.Context, chainID string, valUpdates []abci.ValidatorUpdate, valUpdateID uint64) error {
	packetData := ccv.NewValidatorSetChangePacketData(valUpdates, valUpdateID)
	fmt.Println(packetData.ValsetUpdateId)

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
		clienttypes.Height{}, uint64(ccv.GetTimeoutTimestamp(ctx.BlockTime()).UnixNano()),
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
	chainID, ok := k.GetChannelToChain(ctx, packet.DestinationChannel)
	if !ok {
		return sdkerrors.Wrapf(ccv.ErrInvalidChildChain, "chain ID doesn't exist for channel ID: %s", packet.DestinationChannel)
	}
	if err := ccv.ModuleCdc.UnmarshalJSON(packet.GetData(), &data); err != nil {
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
		valUpdates := k.stakingKeeper.GetValidatorUpdates(ctx)
		if len(valUpdates) != 0 {
			k.SendPacket(ctx, chainID, valUpdates, valUpdateID)
		}
		return false
	})
	// Set the current valset update ID to next block height,
	// in which the validators states are be updated
	k.SetValsetUpdateBlockHeight(ctx, valUpdateID, uint64(ctx.BlockHeight()+1))
	k.IncrementValidatorSetUpdateId(ctx)
}

// OnRecvPacket slashes and jails the given validator in the packet data
func (k Keeper) OnRecvPacket(ctx sdk.Context, packet channeltypes.Packet, data ccv.ValidatorDowntimePacketData) exported.Acknowledgement {
	if chainID, ok := k.GetChannelToChain(ctx, packet.DestinationChannel); !ok {
		ack := channeltypes.NewErrorAcknowledgement(
			fmt.Sprintf("chain ID doesn't exist for channel ID: %s", chainID),
		)
		chanCap, _ := k.scopedKeeper.GetCapability(ctx, host.ChannelCapabilityPath(packet.DestinationPort, packet.DestinationChannel))
		k.channelKeeper.ChanCloseInit(ctx, packet.DestinationPort, packet.DestinationChannel, chanCap)
		return &ack
	}

	// initiate slashing and jailing
	if err := k.HandleConsumerDowntime(ctx, data); err != nil {
		ack := channeltypes.NewErrorAcknowledgement(err.Error())
		return &ack
	}

	ack := channeltypes.NewResultAcknowledgement([]byte{byte(1)})
	return ack
}

// HandleConsumerDowntime gets the validator and the downtime infraction height from the packet data
// validator address and valset upate ID. Then it executes the slashing the and jailing accordingly.
func (k Keeper) HandleConsumerDowntime(ctx sdk.Context, downtimeData ccv.ValidatorDowntimePacketData) error {
	// get the validator consensus address
	consAddr := sdk.ConsAddress(downtimeData.Validator.Address)

	// get the validator data
	validator, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, consAddr)
	if !found {
		return fmt.Errorf("cannot find validator with address %s", consAddr.String())
	}

	// make sure the validator is not yet unbonded;
	// stakingKeeper.Slash() panics otherwise
	if validator.IsUnbonded() {
		return fmt.Errorf("should not be slashing unbonded validator: %s", validator.GetOperator())
	}

	// get the downtime block height from the valsetUpdateID
	blockHeight := k.GetValsetUpdateBlockHeight(ctx, downtimeData.ValsetUpdateId)
	if blockHeight == 0 {
		return fmt.Errorf("cannot find validator update id %d", downtimeData.ValsetUpdateId)
	}

	fmt.Println("Current Block Height: ", ctx.BlockHeight())
	fmt.Println("Infraction Block Height: ", blockHeight)

	// slash and jail the validator
	k.stakingKeeper.Slash(ctx, consAddr, int64(blockHeight), downtimeData.Validator.Power, sdk.NewDec(1).QuoInt64(downtimeData.SlashFraction))
	if !validator.IsJailed() {
		k.stakingKeeper.Jail(ctx, consAddr)
	}

	k.slashingKeeper.JailUntil(ctx, consAddr, ctx.BlockHeader().Time.Add(time.Duration(downtimeData.JailTime)))

	return nil
}
