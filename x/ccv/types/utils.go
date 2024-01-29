package types

import (
	"errors"
	"reflect"
	"sort"
	"strings"
	"time"

	clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v7/modules/core/04-channel/types"
	host "github.com/cosmos/ibc-go/v7/modules/core/24-host"

	errorsmod "cosmossdk.io/errors"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/types/bech32"

	abci "github.com/cometbft/cometbft/abci/types"
	tmprotocrypto "github.com/cometbft/cometbft/proto/tendermint/crypto"
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
		if out[i].Power != out[j].Power {
			return out[i].Power > out[j].Power
		}
		return out[i].PubKey.String() > out[j].PubKey.String()
	})

	return out
}

// TMCryptoPublicKeyToConsAddr converts a TM public key to an SDK public key
// and returns the associated consensus address
func TMCryptoPublicKeyToConsAddr(k tmprotocrypto.PublicKey) (sdk.ConsAddress, error) {
	sdkK, err := cryptocodec.FromTmProtoPublicKey(k)
	if err != nil {
		return nil, err
	}
	return sdk.GetConsAddress(sdkK), nil
}

// SendIBCPacket sends an IBC packet with packetData
// over the source channelID and portID
func SendIBCPacket(
	ctx sdk.Context,
	scopedKeeper ScopedKeeper,
	channelKeeper ChannelKeeper,
	sourceChannelID string,
	sourcePortID string,
	packetData []byte,
	timeoutPeriod time.Duration,
) error {
	_, ok := channelKeeper.GetChannel(ctx, sourcePortID, sourceChannelID)
	if !ok {
		return errorsmod.Wrapf(channeltypes.ErrChannelNotFound, "channel not found for channel ID: %s", sourceChannelID)
	}
	channelCap, ok := scopedKeeper.GetCapability(ctx, host.ChannelCapabilityPath(sourcePortID, sourceChannelID))
	if !ok {
		return errorsmod.Wrap(channeltypes.ErrChannelCapabilityNotFound, "module does not own channel capability")
	}

	_, err := channelKeeper.SendPacket(ctx,
		channelCap,
		sourcePortID,
		sourceChannelID,
		clienttypes.Height{}, //  timeout height disabled
		uint64(ctx.BlockTime().Add(timeoutPeriod).UnixNano()), // timeout timestamp
		packetData,
	)
	return err
}

func NewErrorAcknowledgementWithLog(ctx sdk.Context, err error) channeltypes.Acknowledgement {
	ctx.Logger().Error("IBC ErrorAcknowledgement constructed", "error", err)
	return channeltypes.NewErrorAcknowledgement(err)
}

// AppendMany appends a variable number of byte slices together
func AppendMany(byteses ...[]byte) (out []byte) {
	for _, bytes := range byteses {
		out = append(out, bytes...)
	}
	return out
}

func PanicIfZeroOrNil(x interface{}, nameForPanicMsg string) {
	if x == nil || reflect.ValueOf(x).IsZero() {
		panic("zero or nil value for " + nameForPanicMsg)
	}
}

// GetConsAddrFromBech32 returns a ConsAddress from a Bech32 with an arbitrary prefix
func GetConsAddrFromBech32(bech32str string) (sdk.ConsAddress, error) {
	bech32Addr := strings.TrimSpace(bech32str)
	if len(bech32Addr) == 0 {
		return nil, errors.New("couldn't parse empty input")
	}
	// remove bech32 prefix
	_, addr, err := bech32.DecodeAndConvert(bech32Addr)
	if err != nil {
		return nil, errors.New("couldn't find valid bech32")
	}
	return sdk.ConsAddress(addr), nil
}
