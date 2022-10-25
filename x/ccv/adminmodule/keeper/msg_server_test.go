package keeper_test

import (
	"context"
	"testing"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/x/ccv/adminmodule/keeper"
	"github.com/cosmos/interchain-security/x/ccv/adminmodule/types"
)

func setupMsgServer(t testing.TB) (types.MsgServer, context.Context, *keeper.Keeper) {
	k, ctx := setupKeeper(t)
	return keeper.NewMsgServerImpl(*k), sdk.WrapSDKContext(ctx), k
}
