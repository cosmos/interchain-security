package staking

import (
	"context"
	"encoding/json"

	"cosmossdk.io/core/appmodule"

	"github.com/cosmos/cosmos-sdk/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/types/module"
	"github.com/cosmos/cosmos-sdk/x/staking"
	"github.com/cosmos/cosmos-sdk/x/staking/exported"
	"github.com/cosmos/cosmos-sdk/x/staking/keeper"
	"github.com/cosmos/cosmos-sdk/x/staking/types"

	abci "github.com/cometbft/cometbft/abci/types"
)

var (
	_ module.AppModule           = AppModule{}
	_ module.AppModuleBasic      = AppModuleBasic{}
	_ module.AppModuleSimulation = AppModule{}

	_ module.HasServices     = AppModule{}
	_ module.HasInvariants   = AppModule{}
	_ module.HasABCIGenesis  = AppModule{}
	_ module.HasABCIEndBlock = AppModule{}

	_ appmodule.AppModule       = AppModule{}
	_ appmodule.HasBeginBlocker = AppModule{}
)

// AppModule embeds the Cosmos SDK's x/staking AppModuleBasic.
type AppModuleBasic struct {
	staking.AppModuleBasic
}

// AppModule embeds the Cosmos SDK's x/staking AppModule where we only override
// specific methods.
type AppModule struct {
	// embed the Cosmos SDK's x/staking AppModule
	staking.AppModule

	keeper     keeper.Keeper
	accKeeper  types.AccountKeeper
	bankKeeper types.BankKeeper
}

// NewAppModule creates a new AppModule object using the native x/staking module
// AppModule constructor.
func NewAppModule(
	cdc codec.Codec,
	keeper *keeper.Keeper,
	ak types.AccountKeeper,
	bk types.BankKeeper,
	ls exported.Subspace,
) AppModule {
	stakingAppMod := staking.NewAppModule(cdc, keeper, ak, bk, ls)
	return AppModule{
		AppModule:  stakingAppMod,
		keeper:     *keeper,
		accKeeper:  ak,
		bankKeeper: bk,
	}
}

// InitGenesis delegates the InitGenesis call to the underlying x/staking module,
// however, it returns no validator updates as validator updates will be provided by the provider module.
func (am AppModule) InitGenesis(ctx sdk.Context, cdc codec.JSONCodec, data json.RawMessage) []abci.ValidatorUpdate {
	var genesisState types.GenesisState

	cdc.MustUnmarshalJSON(data, &genesisState)
	_ = am.keeper.InitGenesis(ctx, &genesisState)

	return []abci.ValidatorUpdate{}
}

// EndBlock delegates the EndBlock call to the underlying x/staking module,
// however, it returns no validator updates as validator updates will be provided by the provider module.
func (am AppModule) EndBlock(ctx context.Context) ([]abci.ValidatorUpdate, error) {
	_, err := am.keeper.EndBlocker(ctx)
	// return the error, but no validator updates
	return []abci.ValidatorUpdate{}, err
}
