package keeper_test

import (
	"strings"
	"testing"

	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"

	sdk "github.com/cosmos/cosmos-sdk/types"
	authTypes "github.com/cosmos/cosmos-sdk/x/auth/types"

	testkeeper "github.com/cosmos/interchain-security/v4/testutil/keeper"
	"github.com/cosmos/interchain-security/v4/x/ccv/consumer/types"
	ccvtypes "github.com/cosmos/interchain-security/v4/x/ccv/types"
)

// TestGetEstimatedNextFeeDistribution tests next fee distribution parameters.
func TestGetEstimatedNextFeeDistribution(t *testing.T) {
	keeperParams := testkeeper.NewInMemKeeperParams(t)
	ctx := keeperParams.Ctx

	ctrl := gomock.NewController(t)
	defer ctrl.Finish()
	mocks := testkeeper.NewMockedKeepers(ctrl)
	mockAccountKeeper := mocks.MockAccountKeeper
	mockBankKeeper := mocks.MockBankKeeper
	consumerKeeper := testkeeper.NewInMemConsumerKeeper(keeperParams, mocks)
	consumerKeeper.SetParams(ctx, ccvtypes.DefaultParams())

	// Setup mock account balance
	fracParam := consumerKeeper.GetConsumerRedistributionFrac(ctx)
	fracDec, err := sdk.NewDecFromStr(fracParam)
	require.NoError(t, err)
	feeAmount := sdk.Coin{
		Denom:  "MOCK",
		Amount: sdk.NewInt(100),
	}
	feeAmountCoins := sdk.Coins([]sdk.Coin{feeAmount})
	feeAmountDec := sdk.NewDecCoinsFromCoins(feeAmountCoins...)
	consumerTokens, _ := feeAmountDec.MulDec(fracDec).TruncateDecimal()
	providerTokens := feeAmountCoins.Sub(consumerTokens...)
	mAcc := authTypes.NewModuleAccount(&authTypes.BaseAccount{}, "", "auth")

	// Setup mock calls
	gomock.InOrder(
		mockAccountKeeper.EXPECT().GetModuleAccount(ctx, authTypes.FeeCollectorName).
			Return(mAcc).
			Times(1),
		mockBankKeeper.EXPECT().GetAllBalances(ctx, mAcc.GetAddress()).
			Return(feeAmountCoins).
			Times(1),
	)

	// set next height to be 10 blocks from current
	consumerKeeper.SetBlocksPerDistributionTransmission(ctx, 10)
	expect := types.NextFeeDistributionEstimate{
		NextHeight:           10,
		LastHeight:           0,
		CurrentHeight:        0,
		DistributionFraction: fracParam,
		Total:                feeAmountDec.String(),
		ToProvider:           sdk.NewDecCoinsFromCoins(providerTokens...).String(),
		ToConsumer:           sdk.NewDecCoinsFromCoins(consumerTokens...).String(),
	}

	res := consumerKeeper.GetEstimatedNextFeeDistribution(ctx)
	require.NotEmpty(t, res)
	require.EqualValues(t, expect, res, "fee distribution data does not match")
}

func TestAllowedRewardDenoms(t *testing.T) {
	keeperParams := testkeeper.NewInMemKeeperParams(t)
	ctx := keeperParams.Ctx

	ctrl := gomock.NewController(t)
	defer ctrl.Finish()
	mocks := testkeeper.NewMockedKeepers(ctrl)
	consumerKeeper := testkeeper.NewInMemConsumerKeeper(keeperParams, mocks)
	params := ccvtypes.DefaultParams()
	params.RewardDenoms = []string{"ustake"}
	params.ProviderRewardDenoms = []string{"uatom"}
	consumerKeeper.SetParams(ctx, params)

	transferChannelID := "channel-5"
	consumerKeeper.SetDistributionTransmissionChannel(ctx, transferChannelID)

	allowedDenoms := consumerKeeper.AllowedRewardDenoms(ctx)
	require.Len(t, allowedDenoms, 2)
	require.Equal(t, allowedDenoms[0], "ustake")
	require.True(t, strings.HasPrefix(allowedDenoms[1], "ibc/"))
}
