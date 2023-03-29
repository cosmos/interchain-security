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

// TestParams tests getters/setters for consumer params
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
		consumertypes.DefaultHistoricalEntries,
		consumertypes.DefaultConsumerUnbondingPeriod,
	) // these are the default params, IBC suite independently sets enabled=true

	params := consumerKeeper.GetParams(ctx)
	require.Equal(t, expParams, params)

	newParams := types.NewParams(false, 1000,
		"channel-2", "cosmos19pe9pg5dv9k5fzgzmsrgnw9rl9asf7ddwhu7lm",
		7*24*time.Hour, 25*time.Hour, "0.5", 500, 24*21*time.Hour)
	consumerKeeper.SetParams(ctx, newParams)
	params = consumerKeeper.GetParams(ctx)
	require.Equal(t, newParams, params)

	consumerKeeper.SetBlocksPerDistributionTransmission(ctx, 10)
	gotBPDT := consumerKeeper.GetBlocksPerDistributionTransmission(ctx)
	require.Equal(t, gotBPDT, int64(10))

	consumerKeeper.SetDistributionTransmissionChannel(ctx, "channel-7")
	gotChan := consumerKeeper.GetDistributionTransmissionChannel(ctx)
	require.Equal(t, gotChan, "channel-7")

	consumerKeeper.SetProviderFeePoolAddrStr(ctx, "cosmos1dkas8mu4kyhl5jrh4nzvm65qz588hy9qcz08la")
	gotAddr := consumerKeeper.
		GetProviderFeePoolAddrStr(ctx)
	require.Equal(t, gotAddr, "cosmos1dkas8mu4kyhl5jrh4nzvm65qz588hy9qcz08la")

	consumerKeeper.SetUnbondingPeriod(ctx, time.Hour*24*10)
	storedUnbondingPeriod := consumerKeeper.GetUnbondingPeriod(ctx)
	require.Equal(t, time.Hour*24*10, storedUnbondingPeriod)
}
