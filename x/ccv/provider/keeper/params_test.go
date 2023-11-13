package keeper_test

import (
	"testing"
	"time"

	"cosmossdk.io/math"
	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
	commitmenttypes "github.com/cosmos/ibc-go/v8/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v8/modules/light-clients/07-tendermint"
	"github.com/stretchr/testify/require"

	sdk "github.com/cosmos/cosmos-sdk/types"

	testkeeper "github.com/cosmos/interchain-security/v3/testutil/keeper"
	providertypes "github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
)

// TestParams tests the getting/setting of provider ccv module params.
func TestParams(t *testing.T) {
	// Construct an in-mem keeper with registered key table
	keeperParams := testkeeper.NewInMemKeeperParams(t)
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, keeperParams)
	defer ctrl.Finish()

	defaultParams := providertypes.DefaultParams()
	providerKeeper.SetParams(ctx, defaultParams)
	params, err := providerKeeper.GetParams(ctx)
	require.NoError(t, err)
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
		),
		"0.25",
		7*24*time.Hour,
		5*time.Hour,
		10*time.Minute,
		time.Hour,
		"0.4",
		100,
		sdk.Coin{
			Denom:  "stake",
			Amount: math.NewInt(10000000),
		},
	)
	providerKeeper.SetParams(ctx, newParams)
	params, err = providerKeeper.GetParams(ctx)
	require.NoError(t, err)
	require.Equal(t, newParams, params)
}
