package keeper_test

import (
	"testing"
	"time"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	commitmenttypes "github.com/cosmos/ibc-go/v3/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	"github.com/stretchr/testify/require"
)

func TestParams(t *testing.T) {
	defaultParams := types.DefaultParams()

	cdc, storeKey, paramsSubspace, ctx := testkeeper.SetupInMemKeeper(t)
	testkeeper.SetTemplateClientState(ctx, &paramsSubspace)

	providerKeeper := testkeeper.GetProviderKeeperWithMocks(
		cdc,
		storeKey,
		paramsSubspace,
		&testkeeper.MockScopedKeeper{},
		&testkeeper.MockChannelKeeper{},
		&testkeeper.MockPortKeeper{},
		&testkeeper.MockConnectionKeeper{},
		&testkeeper.MockClientKeeper{},
		&testkeeper.MockStakingKeeper{},
		&testkeeper.MockSlashingKeeper{},
		&testkeeper.MockAccountKeeper{},
	)

	params := providerKeeper.GetParams(ctx)
	require.Equal(t, defaultParams, params)

	newParams := types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
		time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}, true, false))
	providerKeeper.SetParams(ctx, newParams)
	params = providerKeeper.GetParams(ctx)
	require.Equal(t, newParams, params)
}
