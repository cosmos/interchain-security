package keeper_test

import (
	"testing"
	"time"

	capabilitykeeper "github.com/cosmos/cosmos-sdk/x/capability/keeper"
	paramstypes "github.com/cosmos/cosmos-sdk/x/params/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	commitmenttypes "github.com/cosmos/ibc-go/v3/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	"github.com/stretchr/testify/require"
)

func TestParams(t *testing.T) {
	defaultParams := types.DefaultParams()

	// Constuct our own params subspace
	cdc, storeKey, paramsSubspace, ctx := testkeeper.SetupInMemKeeper(t)
	keyTable := paramstypes.NewKeyTable(paramstypes.NewParamSetPair(types.KeyTemplateClient, &ibctmtypes.ClientState{}, func(value interface{}) error { return nil }))
	paramsSubspace = paramsSubspace.WithKeyTable(keyTable)

	expectedClientState :=
		ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
			time.Second*10, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"upgrade", "upgradedIBCState"}, true, true)

	paramsSubspace.Set(ctx, types.KeyTemplateClient, expectedClientState)

	providerKeeper := testkeeper.GetProviderKeeperWithMocks(
		cdc,
		storeKey,
		paramsSubspace,
		capabilitykeeper.ScopedKeeper{},
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
