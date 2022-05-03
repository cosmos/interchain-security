package keeper

import (
	"fmt"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	host "github.com/cosmos/ibc-go/v3/modules/core/24-host"
	"github.com/cosmos/ibc-go/v3/modules/core/exported"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	abci "github.com/tendermint/tendermint/abci/types"
)

func (k Keeper) SendPacket(ctx sdk.Context, chainID string, valUpdates []abci.ValidatorUpdate, valUpdateID uint64, SlashAcks []string) error {

	packetData := ccv.NewValidatorSetChangePacketData(valUpdates, valUpdateID, SlashAcks)
	packetDataBytes := packetData.GetBytes()

	channelID, ok := k.GetChainToChannel(ctx, chainID)
	if !ok {
		return sdkerrors.Wrapf(channeltypes.ErrChannelNotFound, "channel not found for chain ID: %s", chainID)
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
		return sdkerrors.Wrapf(ccv.ErrInvalidConsumerChain, "chain ID doesn't exist for channel ID: %s", packet.DestinationChannel)
	}

	unbondingOps, _ := k.GetUnbondingOpsFromIndex(ctx, chainID, data.ValsetUpdateId)

	for _, unbondingOp := range unbondingOps {
		// remove consumer chain ID from unbonding op record
		unbondingOp.UnbondingConsumerChains, _ = removeStringFromSlice(unbondingOp.UnbondingConsumerChains, chainID)

		// If unbonding op is completely unbonded from all relevant consumer chains
		if len(unbondingOp.UnbondingConsumerChains) == 0 {
			// Attempt to complete unbonding in staking module
			err := k.stakingKeeper.UnbondingOpCanComplete(ctx, unbondingOp.Id)
			if err != nil {
				return err
			}
			// Delete unbonding op
			k.DeleteUnbondingOp(ctx, unbondingOp.Id)
		} else {
			k.SetUnbondingOp(ctx, unbondingOp)
		}
	}

	// clean up index
	k.DeleteUnbondingOpIndex(ctx, chainID, data.ValsetUpdateId)

	return nil
}

func (k Keeper) OnTimeoutPacket(ctx sdk.Context, packet channeltypes.Packet, data ccv.ValidatorSetChangePacketData) error {
	k.SetChannelStatus(ctx, packet.DestinationChannel, ccv.INVALID)
	// TODO: Unbonding everything?
	return nil
}

// EndBlockCallback is called for each consumer chain in Endblock. It sends latest validator updates to each consumer chain
// in a packet over the CCV channel.
func (k Keeper) EndBlockCallback(ctx sdk.Context) {
	valUpdateID := k.GetValidatorSetUpdateId(ctx)
	k.IterateConsumerChains(ctx, func(ctx sdk.Context, chainID string) (stop bool) {
		valUpdates := k.stakingKeeper.GetValidatorUpdates(ctx)
		if len(valUpdates) != 0 {
			k.SendPacket(ctx, chainID, valUpdates, valUpdateID, k.EmptySlashAcks(ctx, chainID))
		}
		return false
	})
	k.SetValsetUpdateBlockHeight(ctx, valUpdateID, uint64(ctx.BlockHeight()+1))
	k.IncrementValidatorSetUpdateId(ctx)
}

// OnRecvPacket slashes and jails the given validator in the packet data
func (k Keeper) OnRecvPacket(ctx sdk.Context, packet channeltypes.Packet, data ccv.SlashPacketData) exported.Acknowledgement {
	// check that the channel is established
	chainID, ok := k.GetChannelToChain(ctx, packet.DestinationChannel)
	if !ok {
		ack := channeltypes.NewErrorAcknowledgement(
			sdkerrors.Wrap(
				channeltypes.ErrInvalidChannelState,
				packet.DestinationChannel,
			).Error(),
		)
		chanCap, _ := k.scopedKeeper.GetCapability(ctx, host.ChannelCapabilityPath(packet.DestinationPort, packet.DestinationChannel))
		k.channelKeeper.ChanCloseInit(ctx, packet.DestinationPort, packet.DestinationChannel, chanCap)
		return &ack
	}

	// apply slashing
	if err := k.HandleConsumerDowntime(ctx, chainID, data); err != nil {
		ack := channeltypes.NewErrorAcknowledgement(err.Error())
		return &ack
	}

	ack := channeltypes.NewResultAcknowledgement([]byte{byte(1)})
	return ack
}

// HandleConsumerDowntime gets the validator and the downtime infraction height from the packet data
// validator address and valset upate ID. Then it executes the slashing the and jailing accordingly.
func (k Keeper) HandleConsumerDowntime(ctx sdk.Context, chainID string, downtimeData ccv.SlashPacketData) error {

	// map VSC ID to infraction height for the given chain ID
	var infractionHeight uint64
	if downtimeData.ValsetUpdateId == 0 {
		infractionHeight = k.GetInitChainHeight(ctx, chainID)
	} else {
		infractionHeight = k.GetValsetUpdateBlockHeight(ctx, downtimeData.ValsetUpdateId)
	}

	if infractionHeight == 0 {
		return fmt.Errorf("cannot find validator update id %d for chain %s", downtimeData.ValsetUpdateId, chainID)
	}

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

	// slash and jail the validator
	k.stakingKeeper.Slash(ctx, consAddr, int64(infractionHeight), downtimeData.Validator.Power, sdk.NewDec(1).QuoInt64(downtimeData.SlashFraction))
	if !validator.IsJailed() {
		k.stakingKeeper.Jail(ctx, consAddr)
	}

	k.slashingKeeper.JailUntil(ctx, consAddr, ctx.BlockHeader().Time.Add(time.Duration(downtimeData.JailTime)))

	// add slashing ack to consumer chain
	k.AppendslashingAck(ctx, chainID, consAddr.String())

	return nil
}
