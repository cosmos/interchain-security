package keeper_test

import (
	"testing"
	"time"

	"github.com/cosmos/cosmos-sdk/codec"
	codectypes "github.com/cosmos/cosmos-sdk/codec/types"
	"github.com/cosmos/cosmos-sdk/store"
	storetypes "github.com/cosmos/cosmos-sdk/store/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"
	v2providerkeeper "github.com/cosmos/interchain-security/v2/x/ccv/provider/keeper"
	v2providertypes "github.com/cosmos/interchain-security/v2/x/ccv/provider/types"
	v1providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	v1ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"
	"github.com/stretchr/testify/require"
	"github.com/tendermint/tendermint/libs/log"
	tmproto "github.com/tendermint/tendermint/proto/tendermint/types"
	tmdb "github.com/tendermint/tm-db"
)

func TestMigrateParamsv1Tov2(t *testing.T) {
	// Setup raw store
	db := tmdb.NewMemDB()
	stateStore := store.NewCommitMultiStore(db)
	storeKey := sdk.NewKVStoreKey(paramtypes.StoreKey)
	memStoreKey := storetypes.NewMemoryStoreKey("mem_key")
	stateStore.MountStoreWithDB(storeKey, sdk.StoreTypeIAVL, db)
	stateStore.MountStoreWithDB(memStoreKey, sdk.StoreTypeMemory, nil)
	require.NoError(t, stateStore.LoadLatestVersion())
	registry := codectypes.NewInterfaceRegistry()
	cdc := codec.NewProtoCodec(registry)
	ctx := sdk.NewContext(stateStore, tmproto.Header{}, false, log.NewNopLogger())
	require.NoError(t, stateStore.LoadLatestVersion())

	// Create new empty subspace
	subspace := paramtypes.NewSubspace(cdc,
		codec.NewLegacyAmino(),
		storeKey,
		memStoreKey,
		paramtypes.ModuleName,
	)

	// Note that new param key table is set in keeper constructor
	subspace = subspace.WithKeyTable(v1providertypes.ParamKeyTable())

	// Set 8 params from v1.0.0
	subspace.Set(ctx, v1providertypes.KeyTemplateClient, v1providertypes.DefaultParams().TemplateClient)
	subspace.Set(ctx, v1providertypes.KeyTrustingPeriodFraction, "0.75")
	subspace.Set(ctx, v1ccvtypes.KeyCCVTimeoutPeriod, time.Hour)
	subspace.Set(ctx, v1providertypes.KeyInitTimeoutPeriod, time.Hour)
	subspace.Set(ctx, v1providertypes.KeyVscTimeoutPeriod, time.Hour)
	subspace.Set(ctx, v1providertypes.KeySlashMeterReplenishPeriod, time.Hour)
	subspace.Set(ctx, v1providertypes.KeySlashMeterReplenishFraction, "0.5")
	subspace.Set(ctx, v1providertypes.KeyMaxThrottledPackets, int64(10))

	// Confirm new param cannot be set with old key table
	require.Panics(t, func() {
		subspace.Set(ctx, v2providertypes.KeyConsumerRewardDenomRegistrationFee, sdk.NewInt64Coin("uatom", 100))
	})

	// Now create new subspace, mocking an upgrade where app initialization happens again
	subspace = paramtypes.NewSubspace(cdc,
		codec.NewLegacyAmino(),
		storeKey,
		memStoreKey,
		paramtypes.ModuleName,
	).WithKeyTable(v2providertypes.ParamKeyTable()) // Use v2 key table, this would be set in keeper constructor upon app init

	// Run migration
	v2providerkeeper.MigrateParamsv1Tov2(ctx, subspace, sdk.NewCoin("uatom", sdk.NewInt(100000)))

	// Use keeper to confirm params are set correctly
	keeper := v2providerkeeper.Keeper{}
	keeper.SetParamSpace(ctx, subspace)

	params := keeper.GetParams(ctx)
	require.Equal(t, v2providertypes.DefaultParams().TemplateClient, params.TemplateClient)
	require.Equal(t, "0.75", params.TrustingPeriodFraction)
	require.Equal(t, time.Hour, params.CcvTimeoutPeriod)
	require.Equal(t, time.Hour, params.InitTimeoutPeriod)
	require.Equal(t, time.Hour, params.VscTimeoutPeriod)
	require.Equal(t, time.Hour, params.SlashMeterReplenishPeriod)
	require.Equal(t, "0.5", params.SlashMeterReplenishFraction)
	require.Equal(t, int64(10), params.MaxThrottledPackets)
	// New param should be set
	require.Equal(t, sdk.NewCoin("uatom", sdk.NewInt(100000)), params.ConsumerRewardDenomRegistrationFee)

	// Set new param to other values
	params.ConsumerRewardDenomRegistrationFee = sdk.NewCoin("uatom", sdk.NewInt(1000000000))
	keeper.SetParams(ctx, params)
	require.Equal(t, sdk.NewCoin("uatom", sdk.NewInt(1000000000)), keeper.GetParams(ctx).ConsumerRewardDenomRegistrationFee)
}
