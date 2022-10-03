package consumer

import (
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	capabilitytypes "github.com/cosmos/cosmos-sdk/x/capability/types"
	transfertypes "github.com/cosmos/ibc-go/v3/modules/apps/transfer/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	porttypes "github.com/cosmos/ibc-go/v3/modules/core/05-port/types"
	host "github.com/cosmos/ibc-go/v3/modules/core/24-host"
	ibcexported "github.com/cosmos/ibc-go/v3/modules/core/exported"
	"github.com/cosmos/interchain-security/x/ccv/consumer/keeper"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
)

// OnChanOpenInit implements the IBCModule interface
// this function is called by the relayer.
func (am AppModule) OnChanOpenInit(
	ctx sdk.Context,
	order channeltypes.Order,
	connectionHops []string,
	portID string,
	channelID string,
	chanCap *capabilitytypes.Capability,
	counterparty channeltypes.Counterparty,
	version string,
) error {
	// ensure provider channel hasn't already been created
	if providerChannel, ok := am.keeper.GetProviderChannel(ctx); ok {
		return sdkerrors.Wrapf(ccv.ErrDuplicateChannel,
			"provider channel: %s already set", providerChannel)
	}

	// Validate parameters
	if err := validateCCVChannelParams(
		ctx, am.keeper, order, portID, version,
	); err != nil {
		return err
	}

	// ensure the counterparty port ID matches the expected provider port ID
	if counterparty.PortId != ccv.ProviderPortID {
		return sdkerrors.Wrapf(porttypes.ErrInvalidPort,
			"invalid counterparty port: %s, expected %s", counterparty.PortId, ccv.ProviderPortID)
	}

	// Claim channel capability passed back by IBC module
	if err := am.keeper.ClaimCapability(
		ctx, chanCap, host.ChannelCapabilityPath(portID, channelID),
	); err != nil {
		return err
	}

	return am.keeper.VerifyProviderChain(ctx, connectionHops)
}

// validateCCVChannelParams validates a ccv channel
func validateCCVChannelParams(
	ctx sdk.Context,
	keeper keeper.Keeper,
	order channeltypes.Order,
	portID string,
	version string,
) error {
	// Only ordered channels allowed
	if order != channeltypes.ORDERED {
		return sdkerrors.Wrapf(channeltypes.ErrInvalidChannelOrdering, "expected %s channel, got %s ", channeltypes.ORDERED, order)
	}

	// the port ID must match the port ID the CCV module is bounded to
	boundPort := keeper.GetPort(ctx)
	if boundPort != portID {
		return sdkerrors.Wrapf(porttypes.ErrInvalidPort, "invalid port: %s, expected %s", portID, boundPort)
	}

	// the version must match the expected version
	if version != ccv.Version {
		return sdkerrors.Wrapf(ccv.ErrInvalidVersion, "got %s, expected %s", version, ccv.Version)
	}
	return nil
}

// OnChanOpenTry implements the IBCModule interface
func (am AppModule) OnChanOpenTry(
	ctx sdk.Context,
	order channeltypes.Order,
	connectionHops []string,
	portID,
	channelID string,
	chanCap *capabilitytypes.Capability,
	counterparty channeltypes.Counterparty,
	counterpartyVersion string,
) (string, error) {
	return "", sdkerrors.Wrap(ccv.ErrInvalidChannelFlow, "channel handshake must be initiated by consumer chain")
}

// OnChanOpenAck implements the IBCModule interface
func (am AppModule) OnChanOpenAck(
	ctx sdk.Context,
	portID,
	channelID string,
	_ string, // Counter party channel ID is unused per spec
	counterpartyMetadata string,
) error {
	// ensure provider channel has not already been created
	if providerChannel, ok := am.keeper.GetProviderChannel(ctx); ok {
		return sdkerrors.Wrapf(ccv.ErrDuplicateChannel,
			"provider channel: %s already established", providerChannel)
	}

	var md providertypes.HandshakeMetadata
	if err := (&md).Unmarshal([]byte(counterpartyMetadata)); err != nil {
		return sdkerrors.Wrapf(ccv.ErrInvalidHandshakeMetadata,
			"error unmarshalling ibc-ack metadata: \n%v; \nmetadata: %v", err, counterpartyMetadata)
	}

	if md.Version != ccv.Version {
		return sdkerrors.Wrapf(ccv.ErrInvalidVersion,
			"invalid counterparty version: %s, expected %s", md.Version, ccv.Version)
	}

	am.keeper.SetProviderFeePoolAddrStr(ctx, md.ProviderFeePoolAddr)

	///////////////////////////////////////////////////
	// Initialize distribution token transfer channel
	//
	// NOTE The handshake for this channel is handled by the ibc-go/transfer
	// module. If the transfer-channel fails here (unlikely) then the transfer
	// channel should be manually created and ccv parameters set accordingly.

	// reuse the connection hops for this channel for the
	// transfer channel being created.
	connHops, err := am.keeper.GetConnectionHops(ctx, portID, channelID)
	if err != nil {
		return err
	}

	distrTransferMsg := channeltypes.NewMsgChannelOpenInit(
		transfertypes.PortID,
		transfertypes.Version,
		channeltypes.UNORDERED,
		connHops,
		transfertypes.PortID,
		"", // signer unused
	)

	resp, err := am.keeper.ChannelOpenInit(ctx, distrTransferMsg)
	if err != nil {
		return err
	}
	am.keeper.SetDistributionTransmissionChannel(ctx, resp.ChannelId)

	return nil
}

// OnChanOpenConfirm implements the IBCModule interface
func (am AppModule) OnChanOpenConfirm(
	ctx sdk.Context,
	portID,
	channelID string,
) error {
	return sdkerrors.Wrap(ccv.ErrInvalidChannelFlow, "channel handshake must be initiated by consumer chain")
}

// OnChanCloseInit implements the IBCModule interface
func (am AppModule) OnChanCloseInit(
	ctx sdk.Context,
	portID,
	channelID string,
) error {
	// allow relayers to close duplicate OPEN channels, if the provider channel has already been established
	if providerChannel, ok := am.keeper.GetProviderChannel(ctx); ok && providerChannel != channelID {
		return nil
	}
	return sdkerrors.Wrap(sdkerrors.ErrInvalidRequest, "user cannot close channel")
}

// OnChanCloseConfirm implements the IBCModule interface
func (am AppModule) OnChanCloseConfirm(
	ctx sdk.Context,
	portID,
	channelID string,
) error {
	return nil
}

// OnRecvPacket implements the IBCModule interface. A successful acknowledgement
// is returned if the packet data is successfully decoded and the receive application
// logic returns without error.
func (am AppModule) OnRecvPacket(
	ctx sdk.Context,
	packet channeltypes.Packet,
	_ sdk.AccAddress,
) ibcexported.Acknowledgement {
	var (
		ack  ibcexported.Acknowledgement
		data ccv.ValidatorSetChangePacketData
	)
	if err := ccv.ModuleCdc.UnmarshalJSON(packet.GetData(), &data); err != nil {
		errAck := channeltypes.NewErrorAcknowledgement(fmt.Sprintf("cannot unmarshal CCV packet data: %s", err.Error()))
		ack = &errAck
	} else {
		ack = am.keeper.OnRecvVSCPacket(ctx, packet, data)
	}

	ctx.EventManager().EmitEvent(
		sdk.NewEvent(
			ccv.EventTypePacket,
			sdk.NewAttribute(sdk.AttributeKeyModule, consumertypes.ModuleName),
			sdk.NewAttribute(ccv.AttributeKeyAckSuccess, fmt.Sprintf("%t", ack != nil)),
		),
	)

	return ack
}

// OnAcknowledgementPacket implements the IBCModule interface
func (am AppModule) OnAcknowledgementPacket(
	ctx sdk.Context,
	packet channeltypes.Packet,
	acknowledgement []byte,
	_ sdk.AccAddress,
) error {
	var ack channeltypes.Acknowledgement
	if err := ccv.ModuleCdc.UnmarshalJSON(acknowledgement, &ack); err != nil {
		return sdkerrors.Wrapf(sdkerrors.ErrUnknownRequest, "cannot unmarshal consumer packet acknowledgement: %v", err)
	}

	if err := am.keeper.OnAcknowledgementPacket(ctx, packet, ack); err != nil {
		return err
	}

	ctx.EventManager().EmitEvent(
		sdk.NewEvent(
			ccv.EventTypePacket,
			sdk.NewAttribute(sdk.AttributeKeyModule, consumertypes.ModuleName),
			sdk.NewAttribute(ccv.AttributeKeyAck, ack.String()),
		),
	)
	switch resp := ack.Response.(type) {
	case *channeltypes.Acknowledgement_Result:
		ctx.EventManager().EmitEvent(
			sdk.NewEvent(
				ccv.EventTypePacket,
				sdk.NewAttribute(ccv.AttributeKeyAckSuccess, string(resp.Result)),
			),
		)
	case *channeltypes.Acknowledgement_Error:
		ctx.EventManager().EmitEvent(
			sdk.NewEvent(
				ccv.EventTypePacket,
				sdk.NewAttribute(ccv.AttributeKeyAckError, resp.Error),
			),
		)
	}
	return nil
}

// OnTimeoutPacket implements the IBCModule interface
func (am AppModule) OnTimeoutPacket(
	ctx sdk.Context,
	packet channeltypes.Packet,
	_ sdk.AccAddress,
) error {
	var data ccv.SlashPacketData
	if err := ccv.ModuleCdc.UnmarshalJSON(packet.GetData(), &data); err != nil {
		return sdkerrors.Wrapf(sdkerrors.ErrUnknownRequest, "cannot unmarshal consumer packet data: %s", err.Error())
	}

	if err := am.keeper.OnTimeoutPacket(ctx, packet, data); err != nil {
		return err
	}

	ctx.EventManager().EmitEvent(
		sdk.NewEvent(
			ccv.EventTypeTimeout,
			sdk.NewAttribute(sdk.AttributeKeyModule, consumertypes.ModuleName),
		),
	)

	return nil
}
