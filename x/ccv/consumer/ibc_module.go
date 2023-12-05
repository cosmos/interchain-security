package consumer

import (
	"fmt"
	"strconv"
	"strings"

	transfertypes "github.com/cosmos/ibc-go/v7/modules/apps/transfer/types"
	channeltypes "github.com/cosmos/ibc-go/v7/modules/core/04-channel/types"
	porttypes "github.com/cosmos/ibc-go/v7/modules/core/05-port/types"
	host "github.com/cosmos/ibc-go/v7/modules/core/24-host"
	ibcexported "github.com/cosmos/ibc-go/v7/modules/core/exported"

	errorsmod "cosmossdk.io/errors"

	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	capabilitytypes "github.com/cosmos/cosmos-sdk/x/capability/types"

	"github.com/cosmos/interchain-security/v3/x/ccv/consumer/keeper"
	consumertypes "github.com/cosmos/interchain-security/v3/x/ccv/consumer/types"
	"github.com/cosmos/interchain-security/v3/x/ccv/types"
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
) (string, error) {
	// set to the default version if the provided version is empty according to the ICS26 spec
	// https://github.com/cosmos/ibc/blob/main/spec/core/ics-026-routing-module/README.md#technical-specification
	if strings.TrimSpace(version) == "" {
		version = types.Version
	}

	// ensure provider channel hasn't already been created
	if providerChannel, ok := am.keeper.GetProviderChannel(ctx); ok {
		return "", errorsmod.Wrapf(types.ErrDuplicateChannel,
			"provider channel: %s already set", providerChannel)
	}

	// Validate parameters
	if err := validateCCVChannelParams(
		ctx, am.keeper, order, portID, version,
	); err != nil {
		return "", err
	}

	// ensure the counterparty port ID matches the expected provider port ID
	if counterparty.PortId != types.ProviderPortID {
		return "", errorsmod.Wrapf(porttypes.ErrInvalidPort,
			"invalid counterparty port: %s, expected %s", counterparty.PortId, types.ProviderPortID)
	}

	// Claim channel capability passed back by IBC module
	if err := am.keeper.ClaimCapability(
		ctx, chanCap, host.ChannelCapabilityPath(portID, channelID),
	); err != nil {
		return "", err
	}

	if err := am.keeper.VerifyProviderChain(ctx, connectionHops); err != nil {
		return "", err
	}

	return version, nil
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
		return errorsmod.Wrapf(channeltypes.ErrInvalidChannelOrdering, "expected %s channel, got %s ", channeltypes.ORDERED, order)
	}

	// the port ID must match the port ID the CCV module is bounded to
	boundPort := keeper.GetPort(ctx)
	if boundPort != portID {
		return errorsmod.Wrapf(porttypes.ErrInvalidPort, "invalid port: %s, expected %s", portID, boundPort)
	}

	// the version must match the expected version
	if version != types.Version {
		return errorsmod.Wrapf(types.ErrInvalidVersion, "got %s, expected %s", version, types.Version)
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
	return "", errorsmod.Wrap(types.ErrInvalidChannelFlow, "channel handshake must be initiated by consumer chain")
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
		return errorsmod.Wrapf(types.ErrDuplicateChannel,
			"provider channel: %s already established", providerChannel)
	}

	var md types.HandshakeMetadata
	if err := (&md).Unmarshal([]byte(counterpartyMetadata)); err != nil {
		return errorsmod.Wrapf(types.ErrInvalidHandshakeMetadata,
			"error unmarshalling ibc-ack metadata: \n%v; \nmetadata: %v", err, counterpartyMetadata)
	}

	if md.Version != types.Version {
		return errorsmod.Wrapf(types.ErrInvalidVersion,
			"invalid counterparty version: %s, expected %s", md.Version, types.Version)
	}

	am.keeper.SetProviderFeePoolAddrStr(ctx, md.ProviderFeePoolAddr)

	///////////////////////////////////////////////////
	// Initialize distribution token transfer channel

	// First check if an existing transfer channel already exists.
	transChannelID := am.keeper.GetDistributionTransmissionChannel(ctx)
	if found := am.keeper.TransferChannelExists(ctx, transChannelID); found {
		return nil
	}

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

	ctx.EventManager().EmitEvent(
		sdk.NewEvent(
			consumertypes.EventTypeFeeTransferChannelOpened,
			sdk.NewAttribute(sdk.AttributeKeyModule, consumertypes.ModuleName),
			sdk.NewAttribute(channeltypes.AttributeKeyChannelID, channelID),
			sdk.NewAttribute(channeltypes.AttributeKeyPortID, transfertypes.PortID),
		),
	)

	return nil
}

// OnChanOpenConfirm implements the IBCModule interface
func (am AppModule) OnChanOpenConfirm(
	ctx sdk.Context,
	portID,
	channelID string,
) error {
	return errorsmod.Wrap(types.ErrInvalidChannelFlow, "channel handshake must be initiated by consumer chain")
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
	return errorsmod.Wrap(sdkerrors.ErrInvalidRequest, "user cannot close channel")
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
	logger := am.keeper.Logger(ctx)
	ack := channeltypes.NewResultAcknowledgement([]byte{byte(1)})

	var data types.ValidatorSetChangePacketData
	var ackErr error
	if err := types.ModuleCdc.UnmarshalJSON(packet.GetData(), &data); err != nil {
		ackErr = errorsmod.Wrapf(sdkerrors.ErrInvalidType, "cannot unmarshal VSCPacket data")
		logger.Error(fmt.Sprintf("%s sequence %d", ackErr.Error(), packet.Sequence))
		ack = channeltypes.NewErrorAcknowledgement(ackErr)
	}

	// only attempt the application logic if the packet data
	// was successfully decoded
	if ack.Success() {
		err := am.keeper.OnRecvVSCPacket(ctx, packet, data)
		if err != nil {
			ack = channeltypes.NewErrorAcknowledgement(err)
			ackErr = err
			logger.Error(fmt.Sprintf("%s sequence %d", ackErr.Error(), packet.Sequence))
		} else {
			logger.Info("successfully handled VSCPacket sequence: %d", packet.Sequence)
		}
	}

	eventAttributes := []sdk.Attribute{
		sdk.NewAttribute(sdk.AttributeKeyModule, types.ModuleName),
		sdk.NewAttribute(types.AttributeValSetUpdateID, strconv.Itoa(int(data.ValsetUpdateId))),
		sdk.NewAttribute(types.AttributeKeyAckSuccess, fmt.Sprintf("%t", ack.Success())),
	}

	if ackErr != nil {
		eventAttributes = append(eventAttributes, sdk.NewAttribute(types.AttributeKeyAckError, ackErr.Error()))
	}

	ctx.EventManager().EmitEvent(
		sdk.NewEvent(
			types.EventTypePacket,
			eventAttributes...,
		),
	)

	// NOTE: acknowledgement will be written synchronously during IBC handler execution.
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
	if err := types.ModuleCdc.UnmarshalJSON(acknowledgement, &ack); err != nil {
		return errorsmod.Wrapf(sdkerrors.ErrUnknownRequest, "cannot unmarshal consumer packet acknowledgement: %v", err)
	}

	if err := am.keeper.OnAcknowledgementPacket(ctx, packet, ack); err != nil {
		return err
	}

	ctx.EventManager().EmitEvent(
		sdk.NewEvent(
			types.EventTypePacket,
			sdk.NewAttribute(sdk.AttributeKeyModule, consumertypes.ModuleName),
			sdk.NewAttribute(types.AttributeKeyAck, ack.String()),
		),
	)
	switch resp := ack.Response.(type) {
	case *channeltypes.Acknowledgement_Result:
		ctx.EventManager().EmitEvent(
			sdk.NewEvent(
				types.EventTypePacket,
				sdk.NewAttribute(types.AttributeKeyAckSuccess, string(resp.Result)),
			),
		)
	case *channeltypes.Acknowledgement_Error:
		ctx.EventManager().EmitEvent(
			sdk.NewEvent(
				types.EventTypePacket,
				sdk.NewAttribute(types.AttributeKeyAckError, resp.Error),
			),
		)
	}
	return nil
}

// OnTimeoutPacket implements the IBCModule interface
// the CCV channel state is changed to CLOSED
// by the IBC module as the channel is ORDERED
func (am AppModule) OnTimeoutPacket(
	ctx sdk.Context,
	packet channeltypes.Packet,
	_ sdk.AccAddress,
) error {
	ctx.EventManager().EmitEvent(
		sdk.NewEvent(
			types.EventTypeTimeout,
			sdk.NewAttribute(sdk.AttributeKeyModule, consumertypes.ModuleName),
		),
	)

	return nil
}
