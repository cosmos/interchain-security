package keeper_test

import (
	"testing"

	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"

	sdk "github.com/cosmos/cosmos-sdk/types"

	testutil "github.com/cosmos/interchain-security/v3/testutil/keeper"
	consumertypes "github.com/cosmos/interchain-security/v3/x/ccv/consumer/types"
	"github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
)

// TestRegisterConsumerRewardDenom tests the RegisterConsumerRewardDenom method.
func TestRegisterConsumerRewardDenom(t *testing.T) {
	// Setup
	providerKeeper, ctx, ctrl, mocks := testutil.GetProviderKeeperAndCtx(t, testutil.NewInMemKeeperParams(t))
	defer ctrl.Finish()
	defaultParams := types.DefaultParams()
	providerKeeper.SetParams(ctx, defaultParams)
	accAddr := sdk.AccAddress([]byte("addr1"))
	gomock.InOrder(
		mocks.MockDistributionKeeper.EXPECT().FundCommunityPool(ctx,
			sdk.NewCoins(defaultParams.ConsumerRewardDenomRegistrationFee), accAddr).Return(nil).Times(2),
	)

	// Register a consumer reward denom, confirm it's persisted as expected
	err := providerKeeper.RegisterConsumerRewardDenom(ctx, "denom1", accAddr)
	require.NoError(t, err)
	require.True(t, providerKeeper.ConsumerRewardDenomExists(ctx, "denom1"))
	allDenoms := providerKeeper.GetAllConsumerRewardDenoms(ctx)
	require.Len(t, allDenoms, 1)
	require.Equal(t, "denom1", allDenoms[0])

	// Register another consumer reward denom, confirm both denoms are persisted as expected
	err = providerKeeper.RegisterConsumerRewardDenom(ctx, "denom2", accAddr)
	require.NoError(t, err)
	require.True(t, providerKeeper.ConsumerRewardDenomExists(ctx, "denom2"))
	allDenoms = providerKeeper.GetAllConsumerRewardDenoms(ctx)
	require.Len(t, allDenoms, 2)
	require.Equal(t, "denom1", allDenoms[0])
	require.Equal(t, "denom2", allDenoms[1])

	// Try to register first consumer reward denom again, confirm it fails
	err = providerKeeper.RegisterConsumerRewardDenom(ctx, "denom1", accAddr)
	require.Error(t, err)
	require.Equal(t, consumertypes.ErrConsumerRewardDenomAlreadyRegistered, err)
}
