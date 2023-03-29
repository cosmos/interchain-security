package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
)

var (
	_ ccv.ConsumerHooks = Keeper{}
)

// Hooks wrapper struct for ConsumerKeeper
type Hooks struct {
	k Keeper
}

// Return the wrapper struct
func (k Keeper) Hooks() Hooks {
	return Hooks{k}
}

func (k Keeper) AfterValidatorBonded(ctx sdk.Context, consAddr sdk.ConsAddress, _ sdk.ValAddress) {
	if k.hooks != nil {
		k.hooks.AfterValidatorBonded(ctx, consAddr, nil)
	}
}
