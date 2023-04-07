package consumer

import (
	"context"
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
	"github.com/cosmos/cosmos-sdk/types/module"
	simtypes "github.com/cosmos/cosmos-sdk/types/simulation"
	porttypes "github.com/cosmos/ibc-go/v4/modules/core/05-port/types"

	"github.com/cosmos/interchain-security/x/ccv/consumer/client/cli"
	"github.com/cosmos/interchain-security/x/ccv/consumer/keeper"

	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
)

var (
	_ module.AppModule      = AppModule{}
	_ porttypes.IBCModule   = AppModule{}
	_ module.AppModuleBasic = AppModuleBasic{}
)

// AppModuleBasic is the IBC Consumer AppModuleBasic
type AppModuleBasic struct{}

// Name implements AppModuleBasic interface
func (AppModuleBasic) Name() string {
	return consumertypes.ModuleName
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
// consumer module.
func (AppModuleBasic) DefaultGenesis(cdc codec.JSONCodec) json.RawMessage {
	return cdc.MustMarshalJSON(consumertypes.DefaultGenesisState())
}

// ValidateGenesis performs genesis state validation for the ibc consumer module.
func (AppModuleBasic) ValidateGenesis(cdc codec.JSONCodec, config client.TxEncodingConfig, bz json.RawMessage) error {
	var data consumertypes.GenesisState
	if err := cdc.UnmarshalJSON(bz, &data); err != nil {
		return fmt.Errorf("failed to unmarshal %s genesis state: %w", consumertypes.ModuleName, err)
	}

	return data.Validate()
}

// RegisterRESTRoutes implements AppModuleBasic interface
func (AppModuleBasic) RegisterRESTRoutes(clientCtx client.Context, rtr *mux.Router) {
}

// RegisterGRPCGatewayRoutes registers the gRPC Gateway routes for the ibc-consumer module.
func (AppModuleBasic) RegisterGRPCGatewayRoutes(clientCtx client.Context, mux *runtime.ServeMux) {
	err := consumertypes.RegisterQueryHandlerClient(context.Background(), mux, consumertypes.NewQueryClient(clientCtx))
	if err != nil {
		// same behavior as in cosmos-sdk
		panic(err)
	}
}

// GetTxCmd implements AppModuleBasic interface
func (AppModuleBasic) GetTxCmd() *cobra.Command {
	return nil
}

// GetQueryCmd implements AppModuleBasic interface
func (AppModuleBasic) GetQueryCmd() *cobra.Command {
	return cli.NewQueryCmd()
}

// AppModule represents the AppModule for this module
type AppModule struct {
	AppModuleBasic
	keeper keeper.Keeper
}

// NewAppModule creates a new consumer module
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
	return consumertypes.QuerierRoute
}

// LegacyQuerierHandler implements the AppModule interface
func (am AppModule) LegacyQuerierHandler(*codec.LegacyAmino) sdk.Querier {
	return nil
}

// RegisterServices registers module services.
// TODO
func (am AppModule) RegisterServices(cfg module.Configurator) {
	consumertypes.RegisterQueryServer(cfg.QueryServer(), am.keeper)
}

// InitGenesis performs genesis initialization for the consumer module. It returns
// no validator updates.
func (am AppModule) InitGenesis(ctx sdk.Context, cdc codec.JSONCodec, data json.RawMessage) []abci.ValidatorUpdate {
	var genesisState consumertypes.GenesisState
	cdc.MustUnmarshalJSON(data, &genesisState)
	return am.keeper.InitGenesis(ctx, &genesisState)
}

// ExportGenesis returns the exported genesis state as raw bytes for the consumer
// module.
func (am AppModule) ExportGenesis(ctx sdk.Context, cdc codec.JSONCodec) json.RawMessage {
	gs := am.keeper.ExportGenesis(ctx)
	return cdc.MustMarshalJSON(gs)
}

// ConsensusVersion implements AppModule/ConsensusVersion.
func (AppModule) ConsensusVersion() uint64 { return 1 }

// BeginBlock implements the AppModule interface
// Set the VSC ID for the subsequent block to the same value as the current block
// Panic if the provider's channel was established and then closed
func (am AppModule) BeginBlock(ctx sdk.Context, req abci.RequestBeginBlock) {
	// Set largest soft opt out validator power
	am.keeper.UpdateLargestSoftOptOutValidatorPower(ctx)

	channelID, found := am.keeper.GetProviderChannel(ctx)
	if found && am.keeper.IsChannelClosed(ctx, channelID) {
		// The CCV channel was established, but it was then closed;
		// the consumer chain is no longer safe, thus it MUST shut down.
		// This is achieved by panicking, similar as it's done in the
		// x/upgrade module of cosmos-sdk.
		channelClosedMsg := fmt.Sprintf("CCV channel %q was closed - shutdown consumer chain since it is not secured anymore", channelID)
		am.keeper.Logger(ctx).Error(channelClosedMsg)
		panic(channelClosedMsg)
	}

	// map next block height to the vscID of the current block height
	blockHeight := uint64(ctx.BlockHeight())
	vID := am.keeper.GetHeightValsetUpdateID(ctx, blockHeight)
	am.keeper.SetHeightValsetUpdateID(ctx, blockHeight+1, vID)
	am.keeper.Logger(ctx).Debug("block height was mapped to vscID", "height", blockHeight+1, "vscID", vID)

	am.keeper.TrackHistoricalInfo(ctx)
}

// EndBlock implements the AppModule interface
// Flush PendingChanges to ABCI, send pending packets, write acknowledgements for packets that have finished unbonding.
//
// TODO: e2e tests confirming behavior with and without standalone -> consumer changeover
func (am AppModule) EndBlock(ctx sdk.Context, req abci.RequestEndBlock) []abci.ValidatorUpdate {
	// If PreCCV state is active, consumer is a previously standalone chain
	// that was just upgraded to include the consumer ccv module, execute changeover logic.
	if am.keeper.IsPreCCV(ctx) {
		initialValUpdates := am.keeper.ChangeoverToConsumer(ctx)
		return initialValUpdates
	}

	// Execute EndBlock logic for the Reward Distribution sub-protocol
	am.keeper.EndBlockRD(ctx)

	// NOTE: Slash packets are queued in BeginBlock via the Slash function
	// Packet ordering is managed by the PendingPackets queue.
	am.keeper.QueueVSCMaturedPackets(ctx)

	// panics on invalid packets and unexpected send errors
	am.keeper.SendPackets(ctx)

	data, ok := am.keeper.GetPendingChanges(ctx)
	if !ok {
		return []abci.ValidatorUpdate{}
	}
	// apply changes to cross-chain validator set
	tendermintUpdates := am.keeper.ApplyCCValidatorChanges(ctx, data.ValidatorUpdates)
	am.keeper.DeletePendingChanges(ctx)

	am.keeper.Logger(ctx).Debug("sending validator updates to consensus engine", "len updates", len(tendermintUpdates))

	return tendermintUpdates
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

// RandomizedParams creates randomized consumer param changes for the simulator.
// TODO
func (AppModule) RandomizedParams(r *rand.Rand) []simtypes.ParamChange {
	return nil
}

// RegisterStoreDecoder registers a decoder for consumer module's types
// TODO
func (am AppModule) RegisterStoreDecoder(sdr sdk.StoreDecoderRegistry) {
}

// WeightedOperations returns the all the consumer module operations with their respective weights.
func (am AppModule) WeightedOperations(_ module.SimulationState) []simtypes.WeightedOperation {
	return nil
}
