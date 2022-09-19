package keeper_test

import (
	"testing"
	"time"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	commitmenttypes "github.com/cosmos/ibc-go/v3/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"
)

// TestParams tests the default params of the keeper, and getting/setting new params.
func TestParams(t *testing.T) {
	defaultParams := types.DefaultParams()

	// Construct an in-mem keeper with a default template client state set
	keeperParams := testkeeper.NewInMemKeeperParams(t)
	ctrl := gomock.NewController(t)
	defer ctrl.Finish()
	mocks := testkeeper.NewMockedKeepers(ctrl)
	ctx := keeperParams.Ctx
	// Populate template client state to test against
	testkeeper.SetTemplateClientState(ctx, keeperParams.ParamsSubspace)
	providerKeeper := testkeeper.NewInMemProviderKeeper(keeperParams, mocks)

	params := providerKeeper.GetParams(ctx)
	require.Equal(t, defaultParams, params)

	newParams := types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
		time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}, true, false))
	providerKeeper.SetParams(ctx, newParams)
	params = providerKeeper.GetParams(ctx)
	require.Equal(t, newParams, params)
}
