package child

import (
	"encoding/json"
	"fmt"
	"math/rand"

	"github.com/gorilla/mux"
	"github.com/grpc-ecosystem/grpc-gateway/runtime"
	"github.com/spf13/cobra"
	abci "github.com/tendermint/tendermint/abci/types"

	"github.com/cosmos/cosmos-sdk/client"
	"github.com/cosmos/cosmos-sdk/codec"
	codectypes "github.com/cosmos/cosmos-sdk/codec/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	"github.com/cosmos/cosmos-sdk/types/module"
	simtypes "github.com/cosmos/cosmos-sdk/types/simulation"
	capabilitytypes "github.com/cosmos/cosmos-sdk/x/capability/types"

	transfertypes "github.com/cosmos/ibc-go/v3/modules/apps/transfer/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	porttypes "github.com/cosmos/ibc-go/v3/modules/core/05-port/types"
	host "github.com/cosmos/ibc-go/v3/modules/core/24-host"
	ibcexported "github.com/cosmos/ibc-go/v3/modules/core/exported"

	"github.com/cosmos/interchain-security/x/ccv/child/keeper"
	"github.com/cosmos/interchain-security/x/ccv/child/types"
	parenttypes "github.com/cosmos/interchain-security/x/ccv/parent/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
)

var (
	_ module.AppModule      = AppModule{}
	_ porttypes.IBCModule   = AppModule{}
	_ module.AppModuleBasic = AppModuleBasic{}
)

// AppModuleBasic is the IBC Child AppModuleBasic
type AppModuleBasic struct{}

// Name implements AppModuleBasic interface
func (AppModuleBasic) Name() string {
	return types.ModuleName
}

// RegisterLegacyAminoCodec implements AppModuleBasic interface
func (AppModuleBasic) RegisterLegacyAminoCodec(cdc *codec.LegacyAmino) {
	// ccv.RegisterLegacyAminoCodec(cdc)
}

// RegisterInterfaces registers module concrete types into protobuf Any.
func (AppModuleBasic) RegisterInterfaces(registry codectypes.InterfaceRegistry) {
	// ccv.RegisterInterfaces(registry)
}

// DefaultGenesis returns default genesis state as raw bytes for the ibc
// child module.
func (AppModuleBasic) DefaultGenesis(cdc codec.JSONCodec) json.RawMessage {
	return cdc.MustMarshalJSON(types.DefaultGenesisState())
}

// ValidateGenesis performs genesis state validation for the ibc child module.
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

// RegisterGRPCGatewayRoutes registers the gRPC Gateway routes for the ibc-child module.
// TODO
func (AppModuleBasic) RegisterGRPCGatewayRoutes(clientCtx client.Context, mux *runtime.ServeMux) {
}

// GetTxCmd implements AppModuleBasic interface
// TODO
func (AppModuleBasic) GetTxCmd() *cobra.Command {
	return nil
}

// GetQueryCmd implements AppModuleBasic interface
// TODO
func (AppModuleBasic) GetQueryCmd() *cobra.Command {
	return nil
}

// AppModule represents the AppModule for this module
type AppModule struct {
	AppModuleBasic
	keeper keeper.Keeper
}

// NewAppModule creates a new child module
func NewAppModule(k keeper.Keeper) AppModule {
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
}

// InitGenesis performs genesis initialization for the child module. It returns
// no validator updates.
func (am AppModule) InitGenesis(ctx sdk.Context, cdc codec.JSONCodec, data json.RawMessage) []abci.ValidatorUpdate {
	var genesisState types.GenesisState
	cdc.MustUnmarshalJSON(data, &genesisState)
	return am.keeper.InitGenesis(ctx, &genesisState)
}

// ExportGenesis returns the exported genesis state as raw bytes for the child
// module.
func (am AppModule) ExportGenesis(ctx sdk.Context, cdc codec.JSONCodec) json.RawMessage {
	gs := am.keeper.ExportGenesis(ctx)
	return cdc.MustMarshalJSON(gs)
}

// ConsensusVersion implements AppModule/ConsensusVersion.
func (AppModule) ConsensusVersion() uint64 { return 1 }

// BeginBlock implements the AppModule interface
// Set the VSC ID for the subsequent block to the same value as the current block
func (am AppModule) BeginBlock(ctx sdk.Context, req abci.RequestBeginBlock) {
	blockHeight := uint64(ctx.BlockHeight())
	vID := am.keeper.GetHeightValsetUpdateID(ctx, blockHeight)
	am.keeper.SetHeightValsetUpdateID(ctx, blockHeight+1, vID)
}

// EndBlock implements the AppModule interface
// Flush PendingChanges to ABCI, and write acknowledgements for any packets that have finished unbonding.
func (am AppModule) EndBlock(ctx sdk.Context, req abci.RequestEndBlock) []abci.ValidatorUpdate {

	// distribution transmission
	err := am.keeper.DistributeToProviderValidatorSet(ctx)
	if err != nil {
		panic(err)
	}

	data, ok := am.keeper.GetPendingChanges(ctx)
	if !ok {
		return []abci.ValidatorUpdate{}
	}
	// apply changes to cross-chain validator set
	am.keeper.ApplyCCValidatorChanges(ctx, data.ValidatorUpdates)
	am.keeper.DeletePendingChanges(ctx)
	am.keeper.UnbondMaturePackets(ctx)

	return data.ValidatorUpdates
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

// RandomizedParams creates randomized child param changes for the simulator.
// TODO
func (AppModule) RandomizedParams(r *rand.Rand) []simtypes.ParamChange {
	return nil
}

// RegisterStoreDecoder registers a decoder for child module's types
// TODO
func (am AppModule) RegisterStoreDecoder(sdr sdk.StoreDecoderRegistry) {
}

// WeightedOperations returns the all the child module operations with their respective weights.
func (am AppModule) WeightedOperations(_ module.SimulationState) []simtypes.WeightedOperation {
	return nil
}

// ValidateChildChannelParams does validation of a newly created ccv channel. A child
// channel must be ORDERED, use the correct port (by default 'child' on this module), and use the current
// supported version.
func ValidateChildChannelParams(
	ctx sdk.Context,
	keeper keeper.Keeper,
	order channeltypes.Order,
	portID string,
	channelID string,
	version string,
) error {
	if order != channeltypes.ORDERED {
		return sdkerrors.Wrapf(channeltypes.ErrInvalidChannelOrdering, "expected %s channel, got %s ", channeltypes.ORDERED, order)
	}

	// Require portID is the portID CCV module is bound to
	boundPort := keeper.GetPort(ctx)
	if boundPort != portID {
		return sdkerrors.Wrapf(porttypes.ErrInvalidPort, "invalid port: %s, expected %s", portID, boundPort)
	}

	if version != ccv.Version {
		return sdkerrors.Wrapf(ccv.ErrInvalidVersion, "got %s, expected %s", version, ccv.Version)
	}
	return nil
}

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
	// ensure parent channel hasn't already been created
	if parentChannel, ok := am.keeper.GetParentChannel(ctx); ok {
		return sdkerrors.Wrapf(ccv.ErrDuplicateChannel,
			"parent channel: %s already set", parentChannel)
	}

	if err := ValidateChildChannelParams(
		ctx, am.keeper, order, portID, channelID, version,
	); err != nil {
		return err
	}

	// Claim channel capability passed back by IBC module
	if err := am.keeper.ClaimCapability(
		ctx, chanCap, host.ChannelCapabilityPath(portID, channelID),
	); err != nil {
		return err
	}

	am.keeper.SetChannelStatus(ctx, channelID, ccv.INITIALIZING)

	return am.keeper.VerifyParentChain(ctx, channelID, connectionHops)
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
	return "", sdkerrors.Wrap(ccv.ErrInvalidChannelFlow, "channel handshake must be initiated by child chain")
}

// OnChanOpenAck implements the IBCModule interface
func (am AppModule) OnChanOpenAck(
	ctx sdk.Context,
	portID,
	channelID string,
	counterpartyMetadata string,
) error {
	// ensure parent channel has already been created
	if parentChannel, ok := am.keeper.GetParentChannel(ctx); ok {
		return sdkerrors.Wrapf(ccv.ErrDuplicateChannel,
			"parent channel: %s already established", parentChannel)
	}

	var md parenttypes.HandshakeMetadata
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
	// NOTE the handshake for this channel is handled by
	//      the ibc-go/transfer module

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
	return sdkerrors.Wrap(ccv.ErrInvalidChannelFlow, "channel handshake must be initiated by child chain")
}

// OnChanCloseInit implements the IBCModule interface
func (am AppModule) OnChanCloseInit(
	ctx sdk.Context,
	portID,
	channelID string,
) error {
	// allow relayers to close duplicate OPEN channels, if the parent channel has already been established
	if parentChannel, ok := am.keeper.GetParentChannel(ctx); ok && parentChannel != channelID {
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
// is returned if the packet data is succesfully decoded and the receive application
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
		ack = am.keeper.OnRecvPacket(ctx, packet, data)
	}

	ctx.EventManager().EmitEvent(
		sdk.NewEvent(
			ccv.EventTypePacket,
			sdk.NewAttribute(sdk.AttributeKeyModule, types.ModuleName),
			sdk.NewAttribute(ccv.AttributeKeyAckSuccess, fmt.Sprintf("%t", ack != nil)),
		),
	)

	// NOTE: In successful case, acknowledgement will be written asynchronously
	// after unbonding period has elapsed.
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
		return sdkerrors.Wrapf(sdkerrors.ErrUnknownRequest, "cannot unmarshal child packet acknowledgement: %v", err)
	}
	var data ccv.SlashPacketData
	if err := ccv.ModuleCdc.UnmarshalJSON(packet.GetData(), &data); err != nil {
		return sdkerrors.Wrapf(sdkerrors.ErrUnknownRequest, "cannot unmarshal child packet data: %s", err.Error())
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
	var data ccv.SlashPacketData
	if err := ccv.ModuleCdc.UnmarshalJSON(packet.GetData(), &data); err != nil {
		return sdkerrors.Wrapf(sdkerrors.ErrUnknownRequest, "cannot unmarshal child packet data: %s", err.Error())
	}

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
