package keeper_test

import (
	"testing"

	"github.com/stretchr/testify/require"
	testkeeper "hello/testutil/keeper"
	"hello/x/hello/types"
)

func TestGetParams(t *testing.T) {
	k, ctx := testkeeper.HelloKeeper(t)
	params := types.DefaultParams()

	k.SetParams(ctx, params)

	require.EqualValues(t, params, k.GetParams(ctx))
}
