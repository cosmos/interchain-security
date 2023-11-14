package keeper_test

import (
	"testing"

	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"
	testutil "github.com/cosmos/interchain-security/v3/testutil/keeper"
	"github.com/cosmos/interchain-security/v3/x/ccv/provider/keeper"
	"github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
	"github.com/stretchr/testify/require"
)

func TestMigrateParams(t *testing.T) {
	params := testutil.NewInMemKeeperParams(t)
	providerKeeper, ctx, ctrl, _ := testutil.GetProviderKeeperAndCtx(t, params)
	defer ctrl.Finish()

	testCases := []struct {
		name          string
		legacyParams  func() paramtypes.Subspace
		expetedParams types.Params
	}{
		{
			"default params",
			func() paramtypes.Subspace {
				subspace := params.ParamsSubspace
				defaultParams := types.DefaultParams()
				subspace.SetParamSet(ctx, &defaultParams)
				return *subspace
			},
			types.DefaultParams(),
		},
	}
	for _, tc := range testCases {
		migrator := keeper.NewMigrator(providerKeeper, tc.legacyParams())
		err := migrator.MigrateParams(ctx)
		require.NoError(t, err)
		params := providerKeeper.GetParams(ctx)
		require.Equal(t, tc.expetedParams, params)
	}
}
