package provider

import (
	"cosmossdk.io/math"
	sdk "github.com/cosmos/cosmos-sdk/types"
	capabilitytypes "github.com/cosmos/cosmos-sdk/x/capability/types"
	"github.com/cosmos/interchain-security/v4/x/ccv/provider/keeper"
	"github.com/cosmos/interchain-security/v4/x/ccv/provider/types"

	ibctransfertypes "github.com/cosmos/ibc-go/v7/modules/apps/transfer/types"
	clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v7/modules/core/04-channel/types"
	porttypes "github.com/cosmos/ibc-go/v7/modules/core/05-port/types"
	"github.com/cosmos/ibc-go/v7/modules/core/exported"
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
	// executes the IBC transfer OnRecv logic
	ack := im.app.OnRecvPacket(ctx, packet, relayer)
	if ack.Success() {

		// check if the packet sender is a consumer chain
		chainID, err := im.keeper.IdentifyConsumerChainIDFromIBCPacket(ctx, packet)
		if err != nil {
			return ack
		}

		// since the transfer succeed, the IBC transfer packet
		// can be safely deserialized
		var data ibctransfertypes.FungibleTokenPacketData
		_ = types.ModuleCdc.UnmarshalJSON(packet.GetData(), &data)

		// check if the recipient is the consumer reward's pool address
		receiver, _ := sdk.AccAddressFromBech32(data.Receiver)
		if receiver.String() != im.keeper.GetConsumerRewardsPoolAddressStr(ctx) {
			return ack
		}

		// parse denom
		var coinDenom string
		if ibctransfertypes.ReceiverChainIsSource(packet.SourcePort, packet.SourceChannel, data.Denom) {
			voucherPrefix := ibctransfertypes.GetDenomPrefix(packet.GetSourcePort(), packet.GetSourceChannel())
			unprefixedDenom := data.Denom[len(voucherPrefix):]

			// coin denomination used in sending from the escrow address
			coinDenom = unprefixedDenom

			// The denomination used to send the coins is either the native denom or the hash of the path
			// if the denomination is not native.
			denomTrace := ibctransfertypes.ParseDenomTrace(unprefixedDenom)
			if denomTrace.Path != "" {
				coinDenom = denomTrace.IBCDenom()
			}
		} else {
			coinDenom = ibctransfertypes.ParseDenomTrace(
				ibctransfertypes.GetPrefixedDenom(
					packet.DestinationPort,
					packet.DestinationChannel,
					data.Denom,
				),
			).IBCDenom()
		}

		coinAmt, _ := math.NewIntFromString(data.Amount)

		// Iterate over the whitelisted consumer denoms
		for _, denom := range im.keeper.GetAllConsumerRewardDenoms(ctx) {
			if denom != coinDenom {
				continue
			}

			// if there is match, update the consumer chain rewards allocation
			alloc := im.keeper.GetConsumerRewardsAllocation(ctx, chainID)
			alloc.Rewards = alloc.Rewards.Add(
				sdk.NewDecCoinsFromCoins(sdk.Coin{
					Denom:  coinDenom,
					Amount: coinAmt,
				})...)
			im.keeper.SetConsumerRewardsAllocation(ctx, chainID, alloc)

			break
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
	return im.app.OnAcknowledgementPacket(ctx, packet, acknowledgement, relayer)
}

// OnTimeoutPacket implements the IBCMiddleware interface
// If fees are not enabled, this callback will default to the ibc-core packet callback
func (im IBCMiddleware) OnTimeoutPacket(
	ctx sdk.Context,
	packet channeltypes.Packet,
	relayer sdk.AccAddress,
) error {
	// call underlying callback
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
	return 0, nil
}

// WriteAcknowledgement implements the ICS4 Wrapper interface
func (im IBCMiddleware) WriteAcknowledgement(
	ctx sdk.Context,
	chanCap *capabilitytypes.Capability,
	packet exported.PacketI,
	ack exported.Acknowledgement,
) error {
	return nil
}

// GetAppVersion returns the application version of the underlying application
func (im IBCMiddleware) GetAppVersion(ctx sdk.Context, portID, channelID string) (string, bool) {
	return "", false
}
