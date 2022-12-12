package utils

import (
	"sort"
	"time"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	host "github.com/cosmos/ibc-go/v3/modules/core/24-host"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	abci "github.com/tendermint/tendermint/abci/types"
	tmprotocrypto "github.com/tendermint/tendermint/proto/tendermint/crypto"
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

	// The list of tendermint updates should hash the same across all consensus nodes
	// that means it is necessary to sort for determinism.
	sort.Slice(out, func(i, j int) bool {
		if out[i].Power > out[j].Power {
			return true
		}
		return out[i].PubKey.String() > out[j].PubKey.String()
	})

	return out
}

func GetChangePubKeyAddress(change abci.ValidatorUpdate) (addr []byte) {
	pk, err := cryptocodec.FromTmProtoPublicKey(change.PubKey)
	if err != nil {
		panic(err)
	}

	return pk.Address()
}

func TMCryptoPublicKeyToConsAddr(k tmprotocrypto.PublicKey) sdk.ConsAddress {
	sdkK, err := cryptocodec.FromTmProtoPublicKey(k)
	if err != nil {
		panic("could not get public key from tm proto public key")
	}
	return sdk.GetConsAddress(sdkK)
}

// SendIBCPacket sends an IBC packet with packetData
// over the source channelID and portID
func SendIBCPacket(
	ctx sdk.Context,
	scopedKeeper ccv.ScopedKeeper,
	channelKeeper ccv.ChannelKeeper,
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
