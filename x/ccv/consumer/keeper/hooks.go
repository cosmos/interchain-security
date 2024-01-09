package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"

	ccv "github.com/cosmos/interchain-security/v3/x/ccv/types"
)

var _ ccv.ConsumerHooks = Keeper{}

// Hooks wrapper struct for ConsumerKeeper
type Hooks struct {
	k Keeper
}

// Return the wrapper struct
func (k Keeper) Hooks() Hooks {
	return Hooks{k}
}

func (k Keeper) AfterValidatorBonded(ctx sdk.Context, consAddr sdk.ConsAddress, valAddr sdk.ValAddress) error {
	if k.hooks != nil {
		err := k.hooks.AfterValidatorBonded(ctx, consAddr, nil)
		return err
	}
	return nil
}
