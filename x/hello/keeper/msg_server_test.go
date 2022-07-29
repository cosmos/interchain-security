package keeper_test

import (
	"context"
	"testing"

	keepertest "github.com/cosmos/interchain-security/testutil/keeper"
	"github.com/cosmos/interchain-security/x/hello/keeper"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/x/hello/types"
)

func setupMsgServer(t testing.TB) (types.MsgServer, context.Context) {
	k, ctx := keepertest.HelloKeeper(t)
	return keeper.NewMsgServerImpl(*k), sdk.WrapSDKContext(ctx)
}
