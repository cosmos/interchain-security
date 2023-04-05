package staking

import (
	"encoding/json"

	abci "github.com/cometbft/cometbft/abci/types"
	"github.com/cosmos/cosmos-sdk/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/types/module"
	"github.com/cosmos/cosmos-sdk/x/auth/exported"
	"github.com/cosmos/cosmos-sdk/x/staking"
	"github.com/cosmos/cosmos-sdk/x/staking/keeper"
	"github.com/cosmos/cosmos-sdk/x/staking/types"
)

// Note: for a democracy consumer, this "democracy staking" keeper is only for governance capabilities,
// where the ccv consumer module is responsible for proof of stake capabilities, validator set updates, etc.

var (
	_ module.AppModule           = AppModule{}
	_ module.AppModuleBasic      = AppModuleBasic{}
	_ module.AppModuleSimulation = AppModule{}
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
func NewAppModule(cdc codec.Codec, stakingkeeper keeper.Keeper, ak types.AccountKeeper, bk types.BankKeeper, ss exported.Subspace) AppModule {
	stakingAppMod := staking.NewAppModule(cdc, &stakingkeeper, ak, bk, ss)
	return AppModule{
		AppModule:  stakingAppMod,
		keeper:     stakingkeeper,
		accKeeper:  ak,
		bankKeeper: bk,
	}
}

// InitGenesis delegates the InitGenesis call to the underlying x/staking module,
// however, it returns no validator updates as validators are tracked via the
// consumer chain's x/cvv/consumer module and so this module is not responsible
// for returning the initial validator set.
func (AppModule) InitGenesis(_ sdk.Context, _ codec.JSONCodec, _ json.RawMessage) []abci.ValidatorUpdate {
	// var genesisState types.GenesisState

	// cdc.MustUnmarshalJSON(data, &genesisState)
	// _ = staking.InitGenesis(ctx, am.keeper, am.accKeeper, am.bankKeeper, &genesisState)

	return []abci.ValidatorUpdate{}
}

// EndBlock delegates the EndBlock call to the underlying x/staking module,
// however, it returns no validator updates as validators are tracked via the
// consumer chain's x/cvv/consumer module and so this module is not responsible
// for returning the initial validator set.
//
// Note: This method does not require any special handling for PreCCV being true
// (as a part of the changeover from standalone -> consumer chain).
// The ccv consumer Endblocker is ordered to run before the staking Endblocker,
// so if PreCCV is true during one block, the ccv consumer Enblocker will return the proper validator updates,
// the PreCCV flag will be toggled to false, and no validator updates should be returned by this method.
func (am AppModule) EndBlock(ctx sdk.Context, _ abci.RequestEndBlock) []abci.ValidatorUpdate {
	_ = am.keeper.BlockValidatorUpdates(ctx)
	return []abci.ValidatorUpdate{}
}
