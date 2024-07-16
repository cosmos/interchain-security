package keeper_test

import (
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	testkeeper "github.com/cosmos/interchain-security/v5/testutil/keeper"
	ccv "github.com/cosmos/interchain-security/v5/x/ccv/types"
)

// TestParams tests getters/setters for consumer params
func TestParams(t *testing.T) {
	consumerKeeper, ctx, ctrl, _ := testkeeper.GetConsumerKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()
	consumerKeeper.SetParams(ctx, ccv.DefaultParams())

	var rewardDenoms []string
	var provideRewardDenoms []string
	expParams := ccv.NewParams(
		false,
		1000,
		"",
		"",
		ccv.DefaultCCVTimeoutPeriod,
		ccv.DefaultTransferTimeoutPeriod,
		ccv.DefaultConsumerRedistributeFrac,
		ccv.DefaultHistoricalEntries,
		ccv.DefaultConsumerUnbondingPeriod,
		ccv.DefaultSoftOptOutThreshold,
		rewardDenoms,
		provideRewardDenoms,
		ccv.DefaultRetryDelayPeriod,
	) // these are the default params, IBC suite independently sets enabled=true

	params := consumerKeeper.GetConsumerParams(ctx)
	require.Equal(t, expParams, params)

	newParams := ccv.NewParams(false, 1000,
		"channel-2", "cosmos19pe9pg5dv9k5fzgzmsrgnw9rl9asf7ddwhu7lm",
		7*24*time.Hour, 25*time.Hour, "0.5", 500, 24*21*time.Hour, "0.05", []string{"untrn"}, []string{"uatom"}, 2*time.Hour)
	consumerKeeper.SetParams(ctx, newParams)
	params = consumerKeeper.GetConsumerParams(ctx)
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
