package provider

import (
	"context"
	"encoding/json"
	"fmt"

	porttypes "github.com/cosmos/ibc-go/v7/modules/core/05-port/types"
	"github.com/grpc-ecosystem/grpc-gateway/runtime"
	"github.com/spf13/cobra"

	"github.com/cosmos/cosmos-sdk/client"
	"github.com/cosmos/cosmos-sdk/codec"
	codectypes "github.com/cosmos/cosmos-sdk/codec/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/types/module"
	simtypes "github.com/cosmos/cosmos-sdk/types/simulation"
	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"

	abci "github.com/cometbft/cometbft/abci/types"

	"github.com/cosmos/interchain-security/v3/x/ccv/provider/client/cli"
	"github.com/cosmos/interchain-security/v3/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
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
	return providertypes.ModuleName
}

// RegisterLegacyAminoCodec implements AppModuleBasic interface
func (AppModuleBasic) RegisterLegacyAminoCodec(cdc *codec.LegacyAmino) {
	providertypes.RegisterLegacyAminoCodec(cdc)
}

// RegisterInterfaces registers module concrete types into protobuf Any.
func (AppModuleBasic) RegisterInterfaces(registry codectypes.InterfaceRegistry) {
	providertypes.RegisterInterfaces(registry)
}

// DefaultGenesis returns default genesis state as raw bytes for the ibc
// provider module.
func (AppModuleBasic) DefaultGenesis(cdc codec.JSONCodec) json.RawMessage {
	return cdc.MustMarshalJSON(providertypes.DefaultGenesisState())
}

// ValidateGenesis performs genesis state validation for the ibc provider module.
func (AppModuleBasic) ValidateGenesis(cdc codec.JSONCodec, config client.TxEncodingConfig, bz json.RawMessage) error {
	var data providertypes.GenesisState
	if err := cdc.UnmarshalJSON(bz, &data); err != nil {
		return fmt.Errorf("failed to unmarshal %s genesis state: %w", providertypes.ModuleName, err)
	}

	return data.Validate()
}

// RegisterGRPCGatewayRoutes registers the gRPC Gateway routes for the ibc-provider module.
func (AppModuleBasic) RegisterGRPCGatewayRoutes(clientCtx client.Context, mux *runtime.ServeMux) {
	err := providertypes.RegisterQueryHandlerClient(context.Background(), mux, providertypes.NewQueryClient(clientCtx))
	if err != nil {
		// same behavior as in cosmos-sdk
		panic(err)
	}
}

// GetTxCmd implements AppModuleBasic interface
func (AppModuleBasic) GetTxCmd() *cobra.Command {
	return cli.GetTxCmd()
}

// GetQueryCmd implements AppModuleBasic interface
func (AppModuleBasic) GetQueryCmd() *cobra.Command {
	return cli.NewQueryCmd()
}

// AppModule represents the AppModule for this module
type AppModule struct {
	AppModuleBasic
	keeper     *keeper.Keeper
	paramSpace paramtypes.Subspace
}

// NewAppModule creates a new provider module
func NewAppModule(k *keeper.Keeper, paramSpace paramtypes.Subspace) AppModule {
	return AppModule{
		keeper:     k,
		paramSpace: paramSpace,
	}
}

// RegisterInvariants implements the AppModule interface
func (AppModule) RegisterInvariants(ir sdk.InvariantRegistry) {
	// TODO
}

// RegisterServices registers module services.
func (am AppModule) RegisterServices(cfg module.Configurator) {
	providertypes.RegisterMsgServer(cfg.MsgServer(), keeper.NewMsgServerImpl(am.keeper))
	providertypes.RegisterQueryServer(cfg.QueryServer(), am.keeper)
}

// InitGenesis performs genesis initialization for the provider module. It returns no validator updates.
// Note: This method along with ValidateGenesis satisfies the CCV spec:
// https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-initg1
func (am AppModule) InitGenesis(ctx sdk.Context, cdc codec.JSONCodec, data json.RawMessage) []abci.ValidatorUpdate {
	var genesisState providertypes.GenesisState
	cdc.MustUnmarshalJSON(data, &genesisState)

	am.keeper.InitGenesis(ctx, &genesisState)

	return []abci.ValidatorUpdate{}
}

// ExportGenesis returns the exported genesis state as raw bytes for the provider
// module.
func (am AppModule) ExportGenesis(ctx sdk.Context, cdc codec.JSONCodec) json.RawMessage {
	gs := am.keeper.ExportGenesis(ctx)
	return cdc.MustMarshalJSON(gs)
}

// ConsensusVersion implements AppModule/ConsensusVersion.
func (AppModule) ConsensusVersion() uint64 { return 3 }

// BeginBlock implements the AppModule interface
func (am AppModule) BeginBlock(ctx sdk.Context, req abci.RequestBeginBlock) {
	// Create clients to consumer chains that are due to be spawned via pending consumer addition proposals
	am.keeper.BeginBlockInit(ctx)
	// Stop and remove state for any consumer chains that are due to be stopped via pending consumer removal proposals
	am.keeper.BeginBlockCCR(ctx)
	// Check for replenishing slash meter before any slash packets are processed for this block
	am.keeper.BeginBlockCIS(ctx)
}

// EndBlock implements the AppModule interface
func (am AppModule) EndBlock(ctx sdk.Context, req abci.RequestEndBlock) []abci.ValidatorUpdate {
	// EndBlock logic needed for the Consumer Initiated Slashing sub-protocol.
	// Important: EndBlockCIS must be called before EndBlockVSU
	am.keeper.EndBlockCIS(ctx)
	// EndBlock logic needed for the Consumer Chain Removal sub-protocol
	am.keeper.EndBlockCCR(ctx)
	// EndBlock logic needed for the Validator Set Update sub-protocol
	am.keeper.EndBlockVSU(ctx)
	// EndBlock logic need for the  Reward Distribution sub-protocol
	am.keeper.EndBlockRD(ctx)

	return []abci.ValidatorUpdate{}
}

// AppModuleSimulation functions

// GenerateGenesisState creates a randomized GenState of the transfer module.
func (AppModule) GenerateGenesisState(simState *module.SimulationState) {
}

// RegisterStoreDecoder registers a decoder for provider module's types
func (am AppModule) RegisterStoreDecoder(sdr sdk.StoreDecoderRegistry) {
}

// WeightedOperations returns the all the provider module operations with their respective weights.
func (am AppModule) WeightedOperations(_ module.SimulationState) []simtypes.WeightedOperation {
	return nil
}
