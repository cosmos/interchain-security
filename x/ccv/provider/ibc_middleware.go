package provider

import (
	capabilitytypes "github.com/cosmos/ibc-go/modules/capability/types"
	ibctransfertypes "github.com/cosmos/ibc-go/v8/modules/apps/transfer/types"
	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v8/modules/core/04-channel/types"
	porttypes "github.com/cosmos/ibc-go/v8/modules/core/05-port/types"
	"github.com/cosmos/ibc-go/v8/modules/core/exported"

	"cosmossdk.io/math"

	sdk "github.com/cosmos/cosmos-sdk/types"

	"github.com/cosmos/interchain-security/v6/x/ccv/provider/keeper"
	"github.com/cosmos/interchain-security/v6/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v6/x/ccv/types"
)

var _ porttypes.Middleware = &IBCMiddleware{}

// IBCMiddleware implements the callbacks for the IBC transfer middleware given the
// provider keeper and the underlying application.
type IBCMiddleware struct {
	app    porttypes.IBCModule
	keeper keeper.Keeper
}

// NewIBCMiddleware creates a new IBCMiddlware given the keeper and underlying application
func NewIBCMiddleware(app porttypes.IBCModule, k keeper.Keeper) IBCMiddleware {
	return IBCMiddleware{
		app:    app,
		keeper: k,
	}
}

// OnChanOpenInit implements the IBCMiddleware interface
func (im IBCMiddleware) OnChanOpenInit(
	ctx sdk.Context,
	order channeltypes.Order,
	connectionHops []string,
	portID string,
	channelID string,
	chanCap *capabilitytypes.Capability,
	counterparty channeltypes.Counterparty,
	version string,
) (string, error) {
	// call underlying app's OnChanOpenInit callback with the appVersion
	return im.app.OnChanOpenInit(ctx, order, connectionHops, portID, channelID, chanCap, counterparty, version)
}

// OnChanOpenTry implements the IBCMiddleware interface
func (im IBCMiddleware) OnChanOpenTry(
	ctx sdk.Context,
	order channeltypes.Order,
	connectionHops []string,
	portID,
	channelID string,
	chanCap *capabilitytypes.Capability,
	counterparty channeltypes.Counterparty,
	counterpartyVersion string,
) (string, error) {
	// call underlying app's OnChanOpenTry callback with the appVersion
	return im.app.OnChanOpenTry(ctx, order, connectionHops, portID, channelID, chanCap, counterparty, counterpartyVersion)
}

// OnChanOpenAck implements the IBCMiddleware interface
func (im IBCMiddleware) OnChanOpenAck(
	ctx sdk.Context,
	portID,
	channelID string,
	counterpartyChannelID string,
	counterpartyVersion string,
) error {
	// call underlying app's OnChanOpenAck callback with the counterparty app version.
	return im.app.OnChanOpenAck(ctx, portID, channelID, counterpartyChannelID, counterpartyVersion)
}

// OnChanOpenConfirm implements the IBCMiddleware interface
func (im IBCMiddleware) OnChanOpenConfirm(
	ctx sdk.Context,
	portID,
	channelID string,
) error {
	// call underlying app's OnChanOpenConfirm callback.
	return im.app.OnChanOpenConfirm(ctx, portID, channelID)
}

// OnChanCloseInit implements the IBCMiddleware interface
func (im IBCMiddleware) OnChanCloseInit(
	ctx sdk.Context,
	portID,
	channelID string,
) error {
	// call underlying app's OnChanCloseInit callback.
	return im.app.OnChanCloseInit(ctx, portID, channelID)
}

// OnChanCloseConfirm implements the IBCMiddleware interface
func (im IBCMiddleware) OnChanCloseConfirm(
	ctx sdk.Context,
	portID,
	channelID string,
) error {
	return im.app.OnChanCloseConfirm(ctx, portID, channelID)
}

// OnRecvPacket executes the IBC transfer. In case of success,
// it verifies if the packet sender is a consumer chain
// and if the received IBC coin is whitelisted. In such instances,
// it appends the coin to the consumer's chain allocation record
func (im IBCMiddleware) OnRecvPacket(
	ctx sdk.Context,
	packet channeltypes.Packet,
	relayer sdk.AccAddress,
) exported.Acknowledgement {
	logger := im.keeper.Logger(ctx)

	// executes the IBC transfer OnRecv logic
	ack := im.app.OnRecvPacket(ctx, packet, relayer)

	// Note that inside the below if condition statement,
	// we know that the IBC transfer succeeded. That entails
	// that the packet data is valid and can be safely
	// deserialized without checking errors.
	if ack.Success() {
		// extract the coin info received from the packet data
		var data ibctransfertypes.FungibleTokenPacketData
		_ = types.ModuleCdc.UnmarshalJSON(packet.GetData(), &data)

		// check if the recipient is the consumer reward's pool address
		receiver, _ := sdk.AccAddressFromBech32(data.Receiver)
		if receiver.String() != im.keeper.GetConsumerRewardsPoolAddressStr(ctx) {
			return ack
		}

		consumerId := ""
		// check if the transfer has the reward memo
		if rewardMemo, err := ccvtypes.GetRewardMemoFromTransferMemo(data.Memo); err != nil {
			// check if the transfer is on a channel with the same underlying
			// client as the CCV channel
			consumerId, err = im.keeper.IdentifyConsumerIdFromIBCPacket(ctx, packet)
			if err != nil {
				if data.Memo == "consumer chain rewards distribution" {
					// log error message
					logger.Error(
						"received token transfer with ICS reward from unknown consumer",
						"packet", packet.String(),
						"fungibleTokenPacketData", data.String(),
						"error", err.Error(),
					)

				}
				return ack
			}
		} else {
			logger.Info("transfer memo:%#+v", rewardMemo)
			consumerId = rewardMemo.ConsumerId
		}

		coinAmt, _ := math.NewIntFromString(data.Amount)
		coinDenom := GetProviderDenom(data.Denom, packet)

		// verify that the coin's denom is a whitelisted consumer denom,
		// and if so, adds it to the consumer chain rewards allocation,
		// otherwise the prohibited coin just stays in the pool forever.
		if im.keeper.ConsumerRewardDenomExists(ctx, coinDenom) {
			alloc := im.keeper.GetConsumerRewardsAllocation(ctx, consumerId)
			alloc.Rewards = alloc.Rewards.Add(
				sdk.NewDecCoinsFromCoins(sdk.Coin{
					Denom:  coinDenom,
					Amount: coinAmt,
				})...)
			im.keeper.SetConsumerRewardsAllocation(ctx, consumerId, alloc)
		}
	}

	return ack
}

// OnAcknowledgementPacket implements the IBCMiddleware interface
// If fees are not enabled, this callback will default to the ibc-core packet callback
func (im IBCMiddleware) OnAcknowledgementPacket(
	ctx sdk.Context,
	packet channeltypes.Packet,
	acknowledgement []byte,
	relayer sdk.AccAddress,
) error {
	// call underlying app's OnAcknowledgementPacket callback.
	return im.app.OnAcknowledgementPacket(ctx, packet, acknowledgement, relayer)
}

// OnTimeoutPacket implements the IBCMiddleware interface
// If fees are not enabled, this callback will default to the ibc-core packet callback
func (im IBCMiddleware) OnTimeoutPacket(
	ctx sdk.Context,
	packet channeltypes.Packet,
	relayer sdk.AccAddress,
) error {
	// call underlying app's OnTimeoutPacket callback.
	return im.app.OnTimeoutPacket(ctx, packet, relayer)
}

// SendPacket implements the ICS4 Wrapper interface
func (im IBCMiddleware) SendPacket(
	sdk.Context,
	*capabilitytypes.Capability,
	string,
	string,
	clienttypes.Height,
	uint64,
	[]byte,
) (uint64, error) {
	panic("should never be called since the IBC middleware doesn't have an ICS4wrapper")
}

// WriteAcknowledgement implements the ICS4 Wrapper interface
func (im IBCMiddleware) WriteAcknowledgement(
	ctx sdk.Context,
	chanCap *capabilitytypes.Capability,
	packet exported.PacketI,
	ack exported.Acknowledgement,
) error {
	panic("should never be called since the IBC middleware doesn't have an ICS4wrapper")
}

// GetAppVersion returns the application version of the underlying application
func (im IBCMiddleware) GetAppVersion(ctx sdk.Context, portID, channelID string) (string, bool) {
	panic("should never be called since the IBC middleware doesn't have an ICS4wrapper")
}

// GetProviderDenom returns the updated given denom according to the given IBC packet
// It follows the same logic than the OnRecvPacket method of the IBC transfer module
// see https://github.com/cosmos/ibc-go/blob/v7.3.2/modules/apps/transfer/keeper/relay.go#L162
func GetProviderDenom(denom string, packet channeltypes.Packet) (providerDenom string) {
	// If the prefix denom corresponds to the packet's source port and channel,
	// returns the base denom
	if ibctransfertypes.ReceiverChainIsSource(packet.GetSourcePort(), packet.GetSourceChannel(), denom) {
		voucherPrefix := ibctransfertypes.GetDenomPrefix(packet.GetSourcePort(), packet.GetSourceChannel())
		unprefixedDenom := denom[len(voucherPrefix):]

		// coin denomination used in sending from the escrow address
		providerDenom = unprefixedDenom

		// The denomination used to send the coins is either the native denom or the hash of the path
		// if the denomination is not native.
		denomTrace := ibctransfertypes.ParseDenomTrace(unprefixedDenom)
		if denomTrace.Path != "" {
			providerDenom = denomTrace.IBCDenom()
		}
		// update the prefix denom according to the packet info
	} else {
		prefixedDenom := ibctransfertypes.GetPrefixedDenom(
			packet.GetDestPort(),
			packet.GetDestChannel(),
			denom,
		)

		providerDenom = ibctransfertypes.ParseDenomTrace(prefixedDenom).IBCDenom()
	}

	return providerDenom
}
