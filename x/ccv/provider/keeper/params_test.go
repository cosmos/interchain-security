package keeper_test

import (
	"testing"
	"time"

	clienttypes "github.com/cosmos/ibc-go/v4/modules/core/02-client/types"
	commitmenttypes "github.com/cosmos/ibc-go/v4/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v4/modules/light-clients/07-tendermint/types"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"
)

// TestParams tests the getting/setting of provider ccv module params.
func TestParams(t *testing.T) {

	// Construct an in-mem keeper with registered key table
	keeperParams := testkeeper.NewInMemKeeperParams(t)
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, keeperParams)
	gomock.InAnyOrder(mocks.MockStakingKeeper.EXPECT().BondDenom(
		ctx).Return("stake").AnyTimes())
	defer ctrl.Finish()

	defaultParams := providertypes.DefaultParams()
	providerKeeper.SetParams(ctx, defaultParams)
	params := providerKeeper.GetParams(ctx)
	require.Equal(t, defaultParams, params)

	newParams := providertypes.NewParams(
		ibctmtypes.NewClientState(
			"",
			ibctmtypes.DefaultTrustLevel,
			0,
			0,
			time.Second*40,
			clienttypes.Height{},
			commitmenttypes.GetSDKSpecs(),
			[]string{"ibc", "upgradedIBCState"},
			true,
			false,
		),
		"0.25",
		7*24*time.Hour,
		5*time.Hour,
		10*time.Minute,
		time.Hour,
		"0.4",
		100,
	)
	providerKeeper.SetParams(ctx, newParams)
	params = providerKeeper.GetParams(ctx)
	require.Equal(t, newParams, params)
}
