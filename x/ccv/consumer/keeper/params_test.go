package keeper_test

import (
	"testing"
	"time"

	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	"github.com/cosmos/interchain-security/x/ccv/consumer/types"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	"github.com/stretchr/testify/require"
)

// TestParams tests the default params set for a consumer chain, and related getters/setters
func TestParams(t *testing.T) {
	consumerKeeper, ctx, ctrl, _ := testkeeper.GetConsumerKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()
	consumerKeeper.SetParams(ctx, types.DefaultParams())

	expParams := types.NewParams(
		false,
		1000,
		"",
		"",
		ccv.DefaultCCVTimeoutPeriod,
		consumertypes.DefaultTransferTimeoutPeriod,
		consumertypes.DefaultConsumerRedistributeFrac,
		consumertypes.DefaultNumHistoricalEntries,
	) // these are the default params, IBC suite independently sets enabled=true

	params := consumerKeeper.GetParams(ctx)
	require.Equal(t, expParams, params)

	newParams := types.NewParams(
		false, 1000, "abc", "def", 7*24*time.Hour, 25*time.Hour, "0.5", 500)
	consumerKeeper.SetParams(ctx, newParams)
	params = consumerKeeper.GetParams(ctx)
	require.Equal(t, newParams, params)

	consumerKeeper.SetBlocksPerDistributionTransmission(ctx, 10)
	gotBPDT := consumerKeeper.GetBlocksPerDistributionTransmission(ctx)
	require.Equal(t, gotBPDT, int64(10))

	consumerKeeper.SetDistributionTransmissionChannel(ctx, "foobarbaz")
	gotChan := consumerKeeper.GetDistributionTransmissionChannel(ctx)
	require.Equal(t, gotChan, "foobarbaz")

	consumerKeeper.SetProviderFeePoolAddrStr(ctx, "foobar")
	gotAddr := consumerKeeper.
		GetProviderFeePoolAddrStr(ctx)
	require.Equal(t, gotAddr, "foobar")
}
