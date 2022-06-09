package utils

import (
	"time"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	capabilitykeeper "github.com/cosmos/cosmos-sdk/x/capability/keeper"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	host "github.com/cosmos/ibc-go/v3/modules/core/24-host"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	abci "github.com/tendermint/tendermint/abci/types"
)

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
	return out
}

func GetChangePubKeyAddress(change abci.ValidatorUpdate) (addr []byte) {
	pk, err := cryptocodec.FromTmProtoPublicKey(change.PubKey)
	if err != nil {
		panic(err)
	}

	return pk.Address()
}

// SendIBCPacket sends an IBC packet with packetData
// over the source channelID and portID
func SendIBCPacket(
	ctx sdk.Context,
	scopedKeeper capabilitykeeper.ScopedKeeper,
	channelKeeper ccv.ChannelKeeper,
	channelID string,
	portID string,
	packetData []byte,
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
		clienttypes.Height{}, uint64(ccv.GetTimeoutTimestamp(ctx.BlockTime()).UnixNano()),
	)
	if err := channelKeeper.SendPacket(ctx, channelCap, packet); err != nil {
		return nil
	}
	return nil
}

// ComputeConsumerUnbondingPeriod computes the unbonding period on the consumer
// from the unbonding period on the provider (providerUnbondingPeriod)
func ComputeConsumerUnbondingPeriod(providerUnbondingPeriod time.Duration) time.Duration {
	if providerUnbondingPeriod > 7*24*time.Hour {
		// In general, the unbonding period on the consumer
		// is one day less than the unbonding period on the provider
		return providerUnbondingPeriod - 24*time.Hour // one day less
	} else if providerUnbondingPeriod >= 24*time.Hour {
		// If the unbonding period on the provider is
		// between one day and one week, then the unbonding period
		// on the consumer is one hour less
		return providerUnbondingPeriod - time.Hour // one hour less
	} else {
		// If the unbonding period on the provider is
		// less than one day, then the unbonding period
		// on the consumer is the same as on the provider
		return providerUnbondingPeriod
	}
}
