package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
)

// HandleOptIn TODO
func (k Keeper) HandleOptIn(ctx sdk.Context, msg types.MsgOptIn) error {
	logger := k.Logger(ctx)
	logger.Info("something ..")

	return nil
}

// HandleOptOut TODO
func (k Keeper) HandleOptOut(ctx sdk.Context, msg types.MsgOptOut) error {
	logger := k.Logger(ctx)
	logger.Info("something ..")

	return nil
}
