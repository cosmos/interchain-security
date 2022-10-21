package keeper

import (
	"fmt"

	"github.com/tendermint/tendermint/libs/log"

	"github.com/cosmos/cosmos-sdk/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	"github.com/cosmos/interchain-security/x/ccv/adminmodule/types"
	// this line is used by starport scaffolding # ibc/keeper/import
)

type (
	Keeper struct {
		cdc                      codec.Codec
		storeKey                 sdk.StoreKey
		memKey                   sdk.StoreKey
		rtr                      govtypes.Router
		IsWhitelistedForProvider func(govtypes.Content) bool
		IsWhitelistedForConsumer func(govtypes.Content) bool
		// this line is used by starport scaffolding # ibc/keeper/attribute
	}
)

func NewKeeper(
	cdc codec.Codec,
	storeKey,
	memKey sdk.StoreKey,
	rtr govtypes.Router,
	isWhitelistedForProvider func(govtypes.Content) bool,
	isWhitelistedForConsumer func(govtypes.Content) bool,
	// this line is used by starport scaffolding # ibc/keeper/parameter
) *Keeper {
	return &Keeper{
		cdc:                      cdc,
		storeKey:                 storeKey,
		memKey:                   memKey,
		rtr:                      rtr,
		IsWhitelistedForProvider: isWhitelistedForProvider,
		IsWhitelistedForConsumer: isWhitelistedForConsumer,
		// this line is used by starport scaffolding # ibc/keeper/return
	}
}

// Router returns the adminmodule Keeper's Router
func (k Keeper) Router() govtypes.Router {
	return k.rtr
}

func (k Keeper) Logger(ctx sdk.Context) log.Logger {
	return ctx.Logger().With("module", fmt.Sprintf("x/%s", types.ModuleName))
}
