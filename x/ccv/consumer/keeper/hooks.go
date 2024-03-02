package keeper

import (
	"context"

	sdk "github.com/cosmos/cosmos-sdk/types"

	ccv "github.com/cosmos/interchain-security/v4/x/ccv/types"
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

func (k Keeper) AfterValidatorBonded(ctx context.Context, consAddr sdk.ConsAddress, valAddr sdk.ValAddress) error {
	if k.hooks != nil {
		err := k.hooks.AfterValidatorBonded(ctx, consAddr, nil)
		return err
	}
	return nil
}
