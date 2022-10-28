package keeper

import (
	"errors"
	"fmt"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	evidencetypes "github.com/cosmos/cosmos-sdk/x/evidence/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"

	"github.com/cosmos/ibc-go/v3/modules/core/exported"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	utils "github.com/cosmos/interchain-security/x/ccv/utils"
)

func removeStringFromSlice(slice []string, x string) (newSlice []string, numRemoved int) {
	for _, y := range slice {
		if x != y {
			newSlice = append(newSlice, y)
		}
	}

	return newSlice, len(slice) - len(newSlice)
}

// OnRecvVSCMaturedPacket handles a VSCMatured packet
func (k Keeper) OnRecvVSCMaturedPacket(
	ctx sdk.Context,
	packet channeltypes.Packet,
	data ccv.VSCMaturedPacketData,
) exported.Acknowledgement {
	// check that the channel is established
	chainID, found := k.GetChannelToChain(ctx, packet.DestinationChannel)
	if !found {
		// VSCMatured packet was sent on a channel different than any of the established CCV channels;
		// this should never happen
		panic(fmt.Errorf("VSCMaturedPacket received on unknown channel %s", packet.DestinationChannel))
	}

	// It is now possible to delete keys from the keymap which the consumer chain
	// is no longer able to reference in slash requests.
	k.KeyMap(ctx, chainID).PruneUnusedKeys(data.ValsetUpdateId)

	// iterate over the unbonding operations mapped to (chainID, data.ValsetUpdateId)
	unbondingOps, _ := k.GetUnbondingOpsFromIndex(ctx, chainID, data.ValsetUpdateId)
	var maturedIds []uint64
	for _, unbondingOp := range unbondingOps {
		// remove consumer chain ID from unbonding op record
		unbondingOp.UnbondingConsumerChains, _ = removeStringFromSlice(unbondingOp.UnbondingConsumerChains, chainID)

		// If unbonding op is completely unbonded from all relevant consumer chains
		if len(unbondingOp.UnbondingConsumerChains) == 0 {
			// Store id of matured unbonding op for later completion of unbonding in staking module
			maturedIds = append(maturedIds, unbondingOp.Id)
			// Delete unbonding op
			k.DeleteUnbondingOp(ctx, unbondingOp.Id)
		} else {
			if err := k.SetUnbondingOp(ctx, unbondingOp); err != nil {
				panic(fmt.Errorf("unbonding op could not be persisted: %w", err))
			}
		}
	}
	if err := k.AppendMaturedUnbondingOps(ctx, maturedIds); err != nil {
		panic(fmt.Errorf("mature unbonding ops could not be appended: %w", err))
	}

	// clean up index
	k.DeleteUnbondingOpIndex(ctx, chainID, data.ValsetUpdateId)

	ack := channeltypes.NewResultAcknowledgement([]byte{byte(1)})
	return ack
}

// CompleteMaturedUnbondingOps attempts to complete all matured unbonding operations
func (k Keeper) CompleteMaturedUnbondingOps(ctx sdk.Context) {
	ids, err := k.ConsumeMaturedUnbondingOps(ctx)
	if err != nil {
		panic(fmt.Sprintf("could not get the list of matured unbonding ops: %s", err.Error()))
	}
	for _, id := range ids {
		// Attempt to complete unbonding in staking module
		err := k.stakingKeeper.UnbondingCanComplete(ctx, id)
		if err != nil {
			panic(fmt.Sprintf("could not complete unbonding op: %s", err.Error()))
		}
	}
}

// OnAcknowledgementPacket handles acknowledgments for sent VSC packets
func (k Keeper) OnAcknowledgementPacket(ctx sdk.Context, packet channeltypes.Packet, ack channeltypes.Acknowledgement) error {
	if err := ack.GetError(); err != "" {
		// The VSC packet data could not be successfully decoded.
		// This should never happen.
		if chainID, ok := k.GetChannelToChain(ctx, packet.SourceChannel); ok {
			// stop consumer chain and uses the LockUnbondingOnTimeout flag
			// to decide whether the unbonding operations should be released
			return k.StopConsumerChain(ctx, chainID, k.GetLockUnbondingOnTimeout(ctx, chainID), false)
		}
		return sdkerrors.Wrapf(types.ErrUnknownConsumerChannelId, "recv ErrorAcknowledgement on unknown channel %s", packet.SourceChannel)
	}
	return nil
}

// OnTimeoutPacket aborts the transaction if no chain exists for the destination channel,
// otherwise it stops the chain
func (k Keeper) OnTimeoutPacket(ctx sdk.Context, packet channeltypes.Packet) error {
	chainID, found := k.GetChannelToChain(ctx, packet.SourceChannel)
	if !found {
		// abort transaction
		return sdkerrors.Wrap(
			channeltypes.ErrInvalidChannelState,
			packet.SourceChannel,
		)
	}
	// stop consumer chain and uses the LockUnbondingOnTimeout flag
	// to decide whether the unbonding operations should be released
	return k.StopConsumerChain(ctx, chainID, k.GetLockUnbondingOnTimeout(ctx, chainID), false)
}

// SendValidatorUpdates sends latest validator updates to every registered consumer chain
func (k Keeper) SendValidatorUpdates(ctx sdk.Context) {
	// get current ValidatorSetUpdateId
	valUpdateID := k.GetValidatorSetUpdateId(ctx)
	// get the validator updates from the staking module
	valUpdates := k.stakingKeeper.GetValidatorUpdates(ctx)
	k.IterateConsumerChains(ctx, func(ctx sdk.Context, chainID, clientID string) (stop bool) {

		packets := k.ConsumePendingVSCs(ctx, chainID)

		// check whether there are changes in the validator set;
		// note that this also entails unbonding operations
		// w/o changes in the voting power of the validators in the validator set
		unbondingOps, _ := k.GetUnbondingOpsFromIndex(ctx, chainID, valUpdateID)
		if len(valUpdates) != 0 || len(unbondingOps) != 0 {

			for _, u := range valUpdates {
				if _, found := k.KeyMap(ctx, chainID).GetCurrentConsumerPubKeyFromProviderPubKey(u.PubKey); !found {
					// The provider has not designated a key to use for the consumer chain. Use the provider key
					// by default.
					k.KeyMap(ctx, chainID).SetProviderPubKeyToConsumerPubKey(u.PubKey, u.PubKey)
				}
			}

			// Map the updates through any key transformations
			updatesToSend := k.KeyMap(ctx, chainID).ComputeUpdates(valUpdateID, valUpdates)

			packets = append(
				packets,
				ccv.NewValidatorSetChangePacketData(updatesToSend, valUpdateID, k.ConsumeSlashAcks(ctx, chainID)),
			)
		}

		// check whether there is an established CCV channel to this consumer chain
		if channelID, found := k.GetChainToChannel(ctx, chainID); found {
			for _, data := range packets {
				// send this validator set change packet data to the consumer chain
				err := utils.SendIBCPacket(
					ctx,
					k.scopedKeeper,
					k.channelKeeper,
					channelID,          // source channel id
					ccv.ProviderPortID, // source port id
					data.GetBytes(),
					k.GetParams(ctx).CcvTimeoutPeriod,
				)
				if err != nil {
					panic(fmt.Errorf("packet could not be sent over IBC: %w", err))
				}
			}
		} else {
			// store the packet data to be sent once the CCV channel is established
			k.SetPendingVSCs(ctx, chainID, packets)
		}
		return false // do not stop the iteration
	})
	k.SetValsetUpdateBlockHeight(ctx, valUpdateID, uint64(ctx.BlockHeight()+1))
	k.IncrementValidatorSetUpdateId(ctx)
}

// OnRecvSlashPacket slashes and jails the given validator in the packet data
func (k Keeper) OnRecvSlashPacket(ctx sdk.Context, packet channeltypes.Packet, data ccv.SlashPacketData) exported.Acknowledgement {
	// check that the channel is established
	chainID, found := k.GetChannelToChain(ctx, packet.DestinationChannel)
	if !found {
		// SlashPacket packet was sent on a channel different than any of the established CCV channels;
		// this should never happen
		panic(fmt.Errorf("SlashPacket received on unknown channel %s", packet.DestinationChannel))
	}

	// apply slashing
	if _, err := k.HandleSlashPacket(ctx, chainID, data); err != nil {
		errAck := channeltypes.NewErrorAcknowledgement(err.Error())
		return &errAck
	}

	ack := channeltypes.NewResultAcknowledgement([]byte{byte(1)})
	return ack
}

// TODO: should this be a panic or an error?
func GetProviderConsAddr(keymap *KeyMap, consumerConsAddress sdk.ConsAddress) (sdk.ConsAddress, error) {
	providerPublicKey, found := keymap.GetProviderPubKeyFromConsumerConsAddress(consumerConsAddress)
	if !found {
		return nil, errors.New("could not find provider address for slashing")
	}
	return PubKeyToConsAddr(providerPublicKey), nil
}

func debugStr(s string, pcons ProviderConsAddr, data ccv.SlashPacketData) {
	p := pcons.String()[14:20]
	fmt.Println(s, "pcons: ", p, data.ValsetUpdateId, data.Infraction == stakingtypes.Downtime)
}

// HandleSlashPacket slash and jail a misbehaving validator according the infraction type
func (k Keeper) HandleSlashPacket(ctx sdk.Context, chainID string, data ccv.SlashPacketData) (success bool, err error) {
	// map VSC ID to infraction height for the given chain ID
	var infractionHeight uint64
	var found bool

	if data.ValsetUpdateId == 0 {
		infractionHeight, found = k.GetInitChainHeight(ctx, chainID)
	} else {
		infractionHeight, found = k.GetValsetUpdateBlockHeight(ctx, data.ValsetUpdateId)
	}

	// return error if we cannot find infraction height matching the validator update id
	if !found {
		return false, fmt.Errorf("cannot find infraction height matching the validator update id %d for chain %s", data.ValsetUpdateId, chainID)
	}

	// TODO: document better
	consumerConsAddr := sdk.ConsAddress(data.Validator.Address)
	providerConsAddr, err := GetProviderConsAddr(k.KeyMap(ctx, chainID), consumerConsAddr)
	// debugStr("recv slash, ", providerConsAddr, data)

	if err != nil {
		fmt.Println("could not find providerConsAddr using keymap lookup")
		return false, nil
	}
	validator, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, providerConsAddr)

	// make sure the validator is not yet unbonded;
	// stakingKeeper.Slash() panics otherwise
	if !found || validator.IsUnbonded() {
		// TODO add warning log message
		// fmt.Sprintf("consumer chain %s trying to slash unbonded validator %s", chainID, consAddr.String())
		return false, nil
	}

	// tombstoned validators should not be slashed multiple times
	if k.slashingKeeper.IsTombstoned(ctx, providerConsAddr) {
		return false, nil
	}

	// slash and jail validator according to their infraction type
	// and using the provider chain parameters
	var (
		jailTime      time.Time
		slashFraction sdk.Dec
	)

	switch data.Infraction {
	case stakingtypes.Downtime:
		// set the downtime slash fraction and duration
		// then append the validator address to the slash ack for its chain id
		slashFraction = k.slashingKeeper.SlashFractionDowntime(ctx)
		jailTime = ctx.BlockTime().Add(k.slashingKeeper.DowntimeJailDuration(ctx))
		k.AppendSlashAck(ctx, chainID, providerConsAddr.String())
	case stakingtypes.DoubleSign:
		// set double-signing slash fraction and infinite jail duration
		// then tombstone the validator
		slashFraction = k.slashingKeeper.SlashFractionDoubleSign(ctx)
		jailTime = evidencetypes.DoubleSignJailEndTime
		k.slashingKeeper.Tombstone(ctx, providerConsAddr)
	default:
		return false, fmt.Errorf("invalid infraction type: %v", data.Infraction)
	}
	// debugStr("actu slash, ", providerConsAddr, data)

	// slash validator
	k.stakingKeeper.Slash(
		ctx,
		providerConsAddr,
		int64(infractionHeight),
		data.Validator.Power,
		slashFraction,
		data.Infraction,
	)

	// jail validator
	if !validator.IsJailed() {
		k.stakingKeeper.Jail(ctx, providerConsAddr)
	}
	k.slashingKeeper.JailUntil(ctx, providerConsAddr, jailTime)

	return true, nil
}
