package keeper_test

import (
	"testing"
	"time"

	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	"github.com/cosmos/interchain-security/x/ccv/consumer/types"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"
	"github.com/stretchr/testify/require"
)

// TestParams tests the default params set for a consumer chain, and related getters/setters
func TestParams(t *testing.T) {
	consumerKeeper, ctx, ctrl, _ := testkeeper.GetConsumerKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()
	consumerKeeper.SetParams(ctx, types.DefaultParams())

	expParams := types.NewParams(false, 1000, "", "", ccvtypes.DefaultCCVTimeoutPeriod, 20*24*time.Hour) // these are the default params, IBC suite independently sets enabled=true

	params := consumerKeeper.GetParams(ctx)
	require.Equal(t, expParams, params)

	newParams := types.NewParams(false, 1000, "abc", "def", time.Hour, 7*24*time.Hour)
	consumerKeeper.SetParams(ctx, newParams)
	params = consumerKeeper.GetParams(ctx)
	require.Equal(t, newParams, params)

	consumerKeeper.SetDistributionTransmissionChannel(ctx, "foobarbaz")
	gotChan := consumerKeeper.GetDistributionTransmissionChannel(ctx)
	require.Equal(t, gotChan, "foobarbaz")

	consumerKeeper.SetProviderFeePoolAddrStr(ctx, "foobar")
	gotAddr := consumerKeeper.
		GetProviderFeePoolAddrStr(ctx)
	require.Equal(t, gotAddr, "foobar")
}
