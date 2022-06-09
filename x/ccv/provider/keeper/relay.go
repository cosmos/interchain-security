package keeper

import (
	"fmt"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	evidencetypes "github.com/cosmos/cosmos-sdk/x/evidence/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"

	host "github.com/cosmos/ibc-go/v3/modules/core/24-host"
	"github.com/cosmos/ibc-go/v3/modules/core/exported"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	utils "github.com/cosmos/interchain-security/x/ccv/utils"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
)

func (k Keeper) SendValidatorSetChangePacket(
	ctx sdk.Context,
	channelID string,
	packetData ccv.ValidatorSetChangePacketData,
) error {
	// send packet over IBC
	return utils.SendIBCPacket(
		ctx,
		k.scopedKeeper,
		k.channelKeeper,
		channelID,    // source channel id
		types.PortID, // source port id
		packetData.GetBytes(),
	)
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
			err := k.stakingKeeper.UnbondingCanComplete(ctx, unbondingOp.Id)
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
	// TODO: Unbonding everything?
	return nil
}

// EndBlockCallback is called for each consumer chain in Endblock. It sends latest validator updates to each consumer chain
// in a packet over the CCV channel.
func (k Keeper) EndBlockCallback(ctx sdk.Context) {
	// get current ValidatorSetUpdateId
	valUpdateID := k.GetValidatorSetUpdateId(ctx)
	fmt.Printf("EndBlockCallback vscID=%d\n", valUpdateID)
	// get the validator updates from the staking module
	valUpdates := k.stakingKeeper.GetValidatorUpdates(ctx)
	k.IterateConsumerChains(ctx, func(ctx sdk.Context, chainID string) (stop bool) {
		// check whether there is an established CCV channel to this consumer chain
		if channelID, found := k.GetChainToChannel(ctx, chainID); found {
			// send all the pending ValidatorSetChangePackets to the consumer chain
			pendingPackets := k.EmptyPendingVSC(ctx, chainID)
			for _, data := range pendingPackets {
				k.SendValidatorSetChangePacket(ctx, channelID, data)
				fmt.Printf("send pending VSC #%d, TS=%s\n", data.ValsetUpdateId, ctx.BlockTime().String())
			}
		}

		// check whether there are changes in the validator set;
		// note that this also entails unbonding operations
		// w/o changes in the voting power of the validators in the validator set
		unbondingOps, _ := k.GetUnbondingOpsFromIndex(ctx, chainID, valUpdateID)
		if len(valUpdates) != 0 || len(unbondingOps) != 0 {
			// construct validator set change packet data
			packetData := ccv.NewValidatorSetChangePacketData(valUpdates, valUpdateID, k.EmptySlashAcks(ctx, chainID))

			// check whether there is an established CCV channel to this consumer chain
			if channelID, found := k.GetChainToChannel(ctx, chainID); found {
				// send this validator set change packet data to the consumer chain
				k.SendValidatorSetChangePacket(ctx, channelID, packetData)
				fmt.Printf("send VSC #%d, TS=%s\n", packetData.ValsetUpdateId, ctx.BlockTime().String())
			} else {
				// store the packet data to be sent once the CCV channel is established
				fmt.Printf("store pending VSC #%d w/ %d updates and %d unbonding ops\n",
					packetData.ValsetUpdateId, len(valUpdates), len(unbondingOps))
				for i, update := range valUpdates {
					valPubKey, _ := cryptocodec.FromTmProtoPublicKey(update.PubKey)
					consAddr := sdk.ConsAddress(valPubKey.Address())
					fmt.Printf(" - [%d] val %s w/ power %d\n", i, consAddr, update.Power)
				}
				k.AppendPendingVSC(ctx, chainID, packetData)
			}
		}
		return false // do not stop the iteration
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
	if err := k.HandleSlashPacket(ctx, chainID, data); err != nil {
		ack := channeltypes.NewErrorAcknowledgement(err.Error())
		return &ack
	}

	ack := channeltypes.NewResultAcknowledgement([]byte{byte(1)})
	return ack
}

// HandleSlashPacket slash and jail a wrong doing validator according the infraction height and type
func (k Keeper) HandleSlashPacket(ctx sdk.Context, chainID string, data ccv.SlashPacketData) error {
	// map VSC ID to infraction height for the given chain ID
	var infractionHeight uint64
	if data.ValsetUpdateId == 0 {
		infractionHeight = k.GetInitChainHeight(ctx, chainID)
	} else {
		infractionHeight = k.GetValsetUpdateBlockHeight(ctx, data.ValsetUpdateId)
	}

	// return if there isn't any initial chain height for the consumer chain
	if infractionHeight == 0 {
		return fmt.Errorf("cannot find validator update id %d for chain %s", data.ValsetUpdateId, chainID)
	}

	// get the validator
	consAddr := sdk.ConsAddress(data.Validator.Address)
	validator, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, consAddr)

	// make sure the validator is not yet unbonded;
	// stakingKeeper.Slash() panics otherwise
	if !found || validator.IsUnbonded() {
		return fmt.Errorf("should not be slashing unbonded validator: %s", validator.GetOperator())
	}

	// spare jailed and/or tombstoned validator preventing to slash it again
	if k.slashingKeeper.IsTombstoned(ctx, consAddr) {
		return fmt.Errorf("should not be slashing jailed and/or tombstoned validator: %s", validator.GetOperator())
	}

	// slash and jail validator according to their infraction type
	// and using the provider chain parameters
	var (
		jailTime      time.Time
		slashFraction sdk.Dec
	)

	switch data.Infraction {
	// set the downtime slash fraction and duration
	// then append the validator address to the slash ack for its chain id
	case stakingtypes.Downtime:
		slashFraction = k.slashingKeeper.SlashFractionDowntime(ctx)
		jailTime = ctx.BlockTime().Add(k.slashingKeeper.DowntimeJailDuration(ctx))
		k.AppendSlashAck(ctx, chainID, consAddr.String())
	// set double-signing slash fraction and infinite jail duration
	// then tombstone the validator
	case stakingtypes.DoubleSign:
		slashFraction = k.slashingKeeper.SlashFractionDoubleSign(ctx)
		jailTime = evidencetypes.DoubleSignJailEndTime
		k.slashingKeeper.Tombstone(ctx, consAddr)
	default:
		return fmt.Errorf("invalid infraction type: %v", data.Infraction)
	}

	// slash validator
	k.stakingKeeper.Slash(
		ctx,
		consAddr,
		int64(infractionHeight),
		data.Validator.Power,
		slashFraction,
		data.Infraction,
	)

	// jail validator
	if !validator.IsJailed() {
		k.stakingKeeper.Jail(ctx, consAddr)
	}
	k.slashingKeeper.JailUntil(ctx, consAddr, jailTime)

	return nil
}
