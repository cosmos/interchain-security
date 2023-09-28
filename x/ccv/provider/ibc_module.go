package provider

import (
	"fmt"

	channeltypes "github.com/cosmos/ibc-go/v7/modules/core/04-channel/types"
	porttypes "github.com/cosmos/ibc-go/v7/modules/core/05-port/types"
	host "github.com/cosmos/ibc-go/v7/modules/core/24-host"
	ibcexported "github.com/cosmos/ibc-go/v7/modules/core/exported"

	errorsmod "cosmossdk.io/errors"

	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	capabilitytypes "github.com/cosmos/cosmos-sdk/x/capability/types"

	"github.com/cosmos/interchain-security/v3/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/v3/x/ccv/types"
)

// OnChanOpenInit implements the IBCModule interface
//
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-coinit1
// Spec Tag: [CCV-PCF-COINIT.1]
func (am AppModule) OnChanOpenInit(
	ctx sdk.Context,
	order channeltypes.Order,
	connectionHops []string,
	portID string,
	channelID string,
	channelCap *capabilitytypes.Capability,
	counterparty channeltypes.Counterparty,
	version string,
) (string, error) {
	return version, errorsmod.Wrap(ccv.ErrInvalidChannelFlow, "channel handshake must be initiated by consumer chain")
}

// OnChanOpenTry implements the IBCModule interface
//
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-cotry1
// Spec tag: [CCV-PCF-COTRY.1]
func (am AppModule) OnChanOpenTry(
	ctx sdk.Context,
	order channeltypes.Order,
	connectionHops []string,
	portID,
	channelID string,
	chanCap *capabilitytypes.Capability,
	counterparty channeltypes.Counterparty,
	counterpartyVersion string,
) (metadata string, err error) {
	// Validate parameters
	if err := validateCCVChannelParams(
		ctx, am.keeper, order, portID,
	); err != nil {
		return "", err
	}

	// ensure the counterparty port ID matches the expected consumer port ID
	if counterparty.PortId != ccv.ConsumerPortID {
		return "", errorsmod.Wrapf(porttypes.ErrInvalidPort,
			"invalid counterparty port: %s, expected %s", counterparty.PortId, ccv.ConsumerPortID)
	}

	// ensure the counter party version matches the expected version
	if counterpartyVersion != ccv.Version {
		return "", errorsmod.Wrapf(
			ccv.ErrInvalidVersion, "invalid counterparty version: got: %s, expected %s",
			counterpartyVersion, ccv.Version)
	}

	// Claim channel capability
	if err := am.keeper.ClaimCapability(
		ctx, chanCap, host.ChannelCapabilityPath(portID, channelID),
	); err != nil {
		return "", err
	}

	if err := am.keeper.VerifyConsumerChain(
		ctx, channelID, connectionHops,
	); err != nil {
		return "", err
	}

	md := ccv.HandshakeMetadata{
		// NOTE that the fee pool collector address string provided to the
		// the consumer chain must be excluded from the blocked addresses
		// blacklist or all all ibc-transfers from the consumer chain to the
		// provider chain will fail
		ProviderFeePoolAddr: am.keeper.GetConsumerRewardsPoolAddressStr(ctx),
		Version:             ccv.Version,
	}
	mdBz, err := (&md).Marshal()
	if err != nil {
		return "", errorsmod.Wrapf(ccv.ErrInvalidHandshakeMetadata,
			"error marshalling ibc-try metadata: %v", err)
	}
	return string(mdBz), nil
}

// validateCCVChannelParams validates a ccv channel
func validateCCVChannelParams(
	ctx sdk.Context,
	keeper *keeper.Keeper,
	order channeltypes.Order,
	portID string,
) error {
	if order != channeltypes.ORDERED {
		return errorsmod.Wrapf(channeltypes.ErrInvalidChannelOrdering, "expected %s channel, got %s ", channeltypes.ORDERED, order)
	}

	// the port ID must match the port ID the CCV module is bounded to
	boundPort := keeper.GetPort(ctx)
	if boundPort != portID {
		return errorsmod.Wrapf(porttypes.ErrInvalidPort, "invalid port: %s, expected %s", portID, boundPort)
	}
	return nil
}

// OnChanOpenAck implements the IBCModule interface
//
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-coack1
// Spec tag: [CCV-PCF-COACK.1]
func (am AppModule) OnChanOpenAck(
	ctx sdk.Context,
	portID,
	channelID string,
	counterpartyChannelID string,
	counterpartyVersion string,
) error {
	return errorsmod.Wrap(ccv.ErrInvalidChannelFlow, "channel handshake must be initiated by consumer chain")
}

// OnChanOpenConfirm implements the IBCModule interface
//
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-coconfirm1
// Spec tag: [CCV-PCF-COCONFIRM.1]
func (am AppModule) OnChanOpenConfirm(
	ctx sdk.Context,
	portID,
	channelID string,
) error {
	err := am.keeper.SetConsumerChain(ctx, channelID)
	if err != nil {
		return err
	}
	return nil
}

// OnChanCloseInit implements the IBCModule interface
func (am AppModule) OnChanCloseInit(
	ctx sdk.Context,
	portID,
	channelID string,
) error {
	// Disallow user-initiated channel closing for provider channels
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
	consumerPacket, err := UnmarshalConsumerPacket(packet)
	if err != nil {
		errAck := ccv.NewErrorAcknowledgementWithLog(ctx, err)
		return &errAck
	}

	// TODO: call ValidateBasic method on consumer packet data
	// See: https://github.com/cosmos/interchain-security/issues/634

	var ack ibcexported.Acknowledgement
	switch consumerPacket.Type {
	case ccv.VscMaturedPacket:
		// handle VSCMaturedPacket
		ack = am.keeper.OnRecvVSCMaturedPacket(ctx, packet, *consumerPacket.GetVscMaturedPacketData())
	case ccv.SlashPacket:
		// handle SlashPacket
		ack = am.keeper.OnRecvSlashPacket(ctx, packet, *consumerPacket.GetSlashPacketData())
	default:
		errAck := ccv.NewErrorAcknowledgementWithLog(ctx, fmt.Errorf("invalid consumer packet type: %q", consumerPacket.Type))
		ack = &errAck
	}

	ctx.EventManager().EmitEvent(
		sdk.NewEvent(
			ccv.EventTypePacket,
			sdk.NewAttribute(sdk.AttributeKeyModule, providertypes.ModuleName),
			sdk.NewAttribute(ccv.AttributeKeyAckSuccess, fmt.Sprintf("%t", ack != nil)),
		),
	)

	return ack
}

func UnmarshalConsumerPacket(packet channeltypes.Packet) (consumerPacket ccv.ConsumerPacketData, err error) {
	return UnmarshalConsumerPacketData(packet.GetData())
}

func UnmarshalConsumerPacketData(packetData []byte) (consumerPacket ccv.ConsumerPacketData, err error) {
	// First try unmarshaling into ccv.ConsumerPacketData type
	if err := ccv.ModuleCdc.UnmarshalJSON(packetData, &consumerPacket); err != nil {
		// If failed, packet should be a v1 slash packet, retry for ConsumerPacketDataV1 packet type
		var v1Packet ccv.ConsumerPacketDataV1
		errV1 := ccv.ModuleCdc.UnmarshalJSON(packetData, &v1Packet)
		if errV1 != nil {
			// If neither worked, return error
			return ccv.ConsumerPacketData{}, errV1
		}

		// VSC matured packets should not be unmarshaled as v1 packets
		if v1Packet.Type == ccv.VscMaturedPacket {
			return ccv.ConsumerPacketData{}, fmt.Errorf("VSC matured packets should be correctly unmarshaled")
		}

		// Convert from v1 packet type
		consumerPacket = ccv.ConsumerPacketData{
			Type: v1Packet.Type,
			Data: &ccv.ConsumerPacketData_SlashPacketData{
				SlashPacketData: v1Packet.GetSlashPacketData().FromV1(),
			},
		}
	}
	return consumerPacket, nil
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
		return errorsmod.Wrapf(sdkerrors.ErrUnknownRequest, "cannot unmarshal provider packet acknowledgement: %v", err)
	}

	if err := am.keeper.OnAcknowledgementPacket(ctx, packet, ack); err != nil {
		return err
	}

	ctx.EventManager().EmitEvent(
		sdk.NewEvent(
			ccv.EventTypePacket,
			sdk.NewAttribute(sdk.AttributeKeyModule, providertypes.ModuleName),
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
	if err := am.keeper.OnTimeoutPacket(ctx, packet); err != nil {
		return err
	}

	ctx.EventManager().EmitEvent(
		sdk.NewEvent(
			ccv.EventTypeTimeout,
			sdk.NewAttribute(sdk.AttributeKeyModule, providertypes.ModuleName),
		),
	)

	return nil
}
