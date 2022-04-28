package provider

import (
	"context"
	"encoding/json"
	"fmt"
	"math/rand"

	"github.com/cosmos/cosmos-sdk/client"
	"github.com/cosmos/cosmos-sdk/codec"
	codectypes "github.com/cosmos/cosmos-sdk/codec/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	"github.com/cosmos/cosmos-sdk/types/module"
	simtypes "github.com/cosmos/cosmos-sdk/types/simulation"
	capabilitytypes "github.com/cosmos/cosmos-sdk/x/capability/types"
	"github.com/gorilla/mux"
	"github.com/grpc-ecosystem/grpc-gateway/runtime"
	"github.com/spf13/cobra"
	abci "github.com/tendermint/tendermint/abci/types"

	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	porttypes "github.com/cosmos/ibc-go/v3/modules/core/05-port/types"
	host "github.com/cosmos/ibc-go/v3/modules/core/24-host"
	ibcexported "github.com/cosmos/ibc-go/v3/modules/core/exported"
	"github.com/cosmos/interchain-security/x/ccv/provider/client/cli"
	"github.com/cosmos/interchain-security/x/ccv/provider/keeper"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
)

var (
	_ module.AppModule      = AppModule{}
	_ porttypes.IBCModule   = AppModule{}
	_ module.AppModuleBasic = AppModuleBasic{}
)

// AppModuleBasic is the IBC Provider AppModuleBasic
type AppModuleBasic struct{}

// Name implements AppModuleBasic interface
func (AppModuleBasic) Name() string {
	return types.ModuleName
}

// RegisterLegacyAminoCodec implements AppModuleBasic interface
func (AppModuleBasic) RegisterLegacyAminoCodec(cdc *codec.LegacyAmino) {
	types.RegisterLegacyAminoCodec(cdc)
}

// RegisterInterfaces registers module concrete types into protobuf Any.
func (AppModuleBasic) RegisterInterfaces(registry codectypes.InterfaceRegistry) {
	types.RegisterInterfaces(registry)
}

// DefaultGenesis returns default genesis state as raw bytes for the ibc
// provider module.
func (AppModuleBasic) DefaultGenesis(cdc codec.JSONCodec) json.RawMessage {
	return cdc.MustMarshalJSON(types.DefaultGenesisState())
}

// ValidateGenesis performs genesis state validation for the ibc provider module.
func (AppModuleBasic) ValidateGenesis(cdc codec.JSONCodec, config client.TxEncodingConfig, bz json.RawMessage) error {
	var data types.GenesisState
	if err := cdc.UnmarshalJSON(bz, &data); err != nil {
		return fmt.Errorf("failed to unmarshal %s genesis state: %w", types.ModuleName, err)
	}

	return data.Validate()
}

// RegisterRESTRoutes implements AppModuleBasic interface
// TODO
func (AppModuleBasic) RegisterRESTRoutes(clientCtx client.Context, rtr *mux.Router) {
}

// RegisterGRPCGatewayRoutes registers the gRPC Gateway routes for the ibc-provider module.
// TODO
func (AppModuleBasic) RegisterGRPCGatewayRoutes(clientCtx client.Context, mux *runtime.ServeMux) {
	types.RegisterQueryHandlerClient(context.Background(), mux, types.NewQueryClient(clientCtx))
}

// GetTxCmd implements AppModuleBasic interface
// TODO
func (AppModuleBasic) GetTxCmd() *cobra.Command {
	return nil
}

// GetQueryCmd implements AppModuleBasic interface
// TODO
func (AppModuleBasic) GetQueryCmd() *cobra.Command {
	return cli.NewQueryCmd()
}

// AppModule represents the AppModule for this module
type AppModule struct {
	AppModuleBasic
	keeper *keeper.Keeper
}

// NewAppModule creates a new provider module
func NewAppModule(k *keeper.Keeper) AppModule {
	return AppModule{
		keeper: k,
	}
}

// RegisterInvariants implements the AppModule interface
func (AppModule) RegisterInvariants(ir sdk.InvariantRegistry) {
	// TODO
}

// Route implements the AppModule interface
func (am AppModule) Route() sdk.Route {
	return sdk.Route{}
}

// QuerierRoute implements the AppModule interface
func (AppModule) QuerierRoute() string {
	return types.QuerierRoute
}

// LegacyQuerierHandler implements the AppModule interface
func (am AppModule) LegacyQuerierHandler(*codec.LegacyAmino) sdk.Querier {
	return nil
}

// RegisterServices registers module services.
// TODO
func (am AppModule) RegisterServices(cfg module.Configurator) {
	types.RegisterQueryServer(cfg.QueryServer(), am.keeper)
}

// InitGenesis performs genesis initialization for the provider module. It returns
// no validator updates.
func (am AppModule) InitGenesis(ctx sdk.Context, cdc codec.JSONCodec, data json.RawMessage) []abci.ValidatorUpdate {
	var genesisState types.GenesisState
	cdc.MustUnmarshalJSON(data, &genesisState)
	am.keeper.InitGenesis(ctx, &genesisState)
	// initialize validator update id
	// TODO: Include in genesis and initialize from genesis value
	am.keeper.SetValidatorSetUpdateId(ctx, 1)
	return []abci.ValidatorUpdate{}
}

// ExportGenesis returns the exported genesis state as raw bytes for the provider
// module.
func (am AppModule) ExportGenesis(ctx sdk.Context, cdc codec.JSONCodec) json.RawMessage {
	gs := am.keeper.ExportGenesis(ctx)
	return cdc.MustMarshalJSON(gs)
}

// ConsensusVersion implements AppModule/ConsensusVersion.
func (AppModule) ConsensusVersion() uint64 { return 1 }

// BeginBlock implements the AppModule interface
func (am AppModule) BeginBlock(ctx sdk.Context, req abci.RequestBeginBlock) {
	// Check if there are any consumer chains that are due to be started
	am.keeper.IteratePendingClientInfo(ctx)
}

// EndBlock implements the AppModule interface
func (am AppModule) EndBlock(ctx sdk.Context, req abci.RequestEndBlock) []abci.ValidatorUpdate {
	// For each consumer chain, call the endblock method which gets relevant validator set changes and
	// sends them to the consumer chain
	am.keeper.EndBlockCallback(ctx)
	return []abci.ValidatorUpdate{}
}

// AppModuleSimulation functions

// GenerateGenesisState creates a randomized GenState of the transfer module.
// TODO
func (AppModule) GenerateGenesisState(simState *module.SimulationState) {
}

// ProposalContents doesn't return any content functions for governance proposals.
func (AppModule) ProposalContents(_ module.SimulationState) []simtypes.WeightedProposalContent {
	return nil
}

// RandomizedParams creates randomized provider param changes for the simulator.
// TODO
func (AppModule) RandomizedParams(r *rand.Rand) []simtypes.ParamChange {
	return nil
}

// RegisterStoreDecoder registers a decoder for provider module's types
// TODO
func (am AppModule) RegisterStoreDecoder(sdr sdk.StoreDecoderRegistry) {
}

// WeightedOperations returns the all the provider module operations with their respective weights.
func (am AppModule) WeightedOperations(_ module.SimulationState) []simtypes.WeightedOperation {
	return nil
}

// ValidateProviderChannelParams does validation of a newly created ccv channel. A provider
// channel must be ORDERED, use the correct port (by default 'provider' on this module), and use the current
// supported version.
func ValidateProviderChannelParams(
	ctx sdk.Context,
	keeper *keeper.Keeper,
	order channeltypes.Order,
	portID string,
	channelID string,
) error {
	if order != channeltypes.ORDERED {
		return sdkerrors.Wrapf(channeltypes.ErrInvalidChannelOrdering, "expected %s channel, got %s ", channeltypes.ORDERED, order)
	}

	// Require portID is the portID CCV module is bound to
	boundPort := keeper.GetPort(ctx)
	if boundPort != portID {
		return sdkerrors.Wrapf(porttypes.ErrInvalidPort, "invalid port: %s, expected %s", portID, boundPort)
	}
	return nil
}

// OnChanOpenInit implements the IBCModule interface
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
	return sdkerrors.Wrap(ccv.ErrInvalidChannelFlow, "channel handshake must be initiated by consumer chain")
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
) (metadata string, err error) {

	if err := ValidateProviderChannelParams(
		ctx, am.keeper, order, portID, channelID,
	); err != nil {
		return "", err
	}

	if counterpartyVersion != ccv.Version {
		return "", sdkerrors.Wrapf(
			ccv.ErrInvalidVersion, "invalid counterparty version: got: %s, expected %s",
			counterpartyVersion, ccv.Version)
	}

	// Module may have already claimed capability in OnChanOpenInit in the case of crossing hellos
	// (ie chainA and chainB both call ChanOpenInit before one of them calls ChanOpenTry)
	// If module can already authenticate the capability then module already owns it so we don't need to claim
	// Otherwise, module does not have channel capability and we must claim it from IBC
	if !am.keeper.AuthenticateCapability(ctx, chanCap, host.ChannelCapabilityPath(portID, channelID)) {
		// Only claim channel capability passed back by IBC module if we do not already own it
		if err := am.keeper.ClaimCapability(ctx, chanCap, host.ChannelCapabilityPath(portID, channelID)); err != nil {
			return "", err
		}
	}

	am.keeper.SetChannelStatus(ctx, channelID, ccv.INITIALIZING)

	if err := am.keeper.VerifyConsumerChain(
		ctx, channelID, connectionHops,
	); err != nil {
		return "", err
	}

	md := types.HandshakeMetadata{
		// NOTE that the fee pool collector address string provided to the
		// the consumer chain must be excluded from the blocked addresses
		// blacklist or all all ibc-transfers from the consumer chain to the
		// provider chain will fail
		ProviderFeePoolAddr: am.keeper.GetFeeCollectorAddressStr(ctx),
		Version:             ccv.Version,
	}
	mdBz, err := (&md).Marshal()
	if err != nil {
		return "", sdkerrors.Wrapf(ccv.ErrInvalidHandshakeMetadata,
			"error marshalling ibc-try metadata: %v", err)
	}
	return string(mdBz), nil
}

// OnChanOpenAck implements the IBCModule interface
func (am AppModule) OnChanOpenAck(
	ctx sdk.Context,
	portID,
	channelID string,
	counterpartyVersion string,
) error {
	return sdkerrors.Wrap(ccv.ErrInvalidChannelFlow, "channel handshake must be initiated by consumer chain")
}

// OnChanOpenConfirm implements the IBCModule interface
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
// is returned if the packet data is succesfully decoded and the receive application
// logic returns without error.
func (am AppModule) OnRecvPacket(
	ctx sdk.Context,
	packet channeltypes.Packet,
	_ sdk.AccAddress,
) ibcexported.Acknowledgement {
	var (
		ack  ibcexported.Acknowledgement
		data ccv.SlashPacketData
	)
	if err := ccv.ModuleCdc.UnmarshalJSON(packet.GetData(), &data); err != nil {
		errAck := channeltypes.NewErrorAcknowledgement(fmt.Sprintf("cannot unmarshal CCV packet data: %s", err.Error()))
		ack = &errAck
	} else {
		ack = am.keeper.OnRecvPacket(ctx, packet, data)
	}

	ctx.EventManager().EmitEvent(
		sdk.NewEvent(
			ccv.EventTypePacket,
			sdk.NewAttribute(sdk.AttributeKeyModule, types.ModuleName),
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
		return sdkerrors.Wrapf(sdkerrors.ErrUnknownRequest, "cannot unmarshal provider packet acknowledgement: %v", err)
	}
	var data ccv.ValidatorSetChangePacketData
	if err := ccv.ModuleCdc.UnmarshalJSON(packet.GetData(), &data); err != nil {
		return sdkerrors.Wrapf(sdkerrors.ErrUnknownRequest, "cannot unmarshal provider packet data: %s", err.Error())
	}

	if err := am.keeper.OnAcknowledgementPacket(ctx, packet, data, ack); err != nil {
		return err
	}

	ctx.EventManager().EmitEvent(
		sdk.NewEvent(
			ccv.EventTypePacket,
			sdk.NewAttribute(sdk.AttributeKeyModule, types.ModuleName),
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
	var data ccv.ValidatorSetChangePacketData
	if err := ccv.ModuleCdc.UnmarshalJSON(packet.GetData(), &data); err != nil {
		return sdkerrors.Wrapf(sdkerrors.ErrUnknownRequest, "cannot unmarshal provider packet data: %s", err.Error())
	}
	// refund tokens
	if err := am.keeper.OnTimeoutPacket(ctx, packet, data); err != nil {
		return err
	}

	ctx.EventManager().EmitEvent(
		sdk.NewEvent(
			ccv.EventTypeTimeout,
			sdk.NewAttribute(sdk.AttributeKeyModule, types.ModuleName),
		),
	)

	return nil
}
