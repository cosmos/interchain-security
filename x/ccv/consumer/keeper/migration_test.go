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
	v2consumerkeeper "github.com/cosmos/interchain-security/v2/x/ccv/consumer/keeper"
	v2consumertypes "github.com/cosmos/interchain-security/v2/x/ccv/consumer/types"
	v1consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
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
	subspace = subspace.WithKeyTable(v1consumertypes.ParamKeyTable())

	// Set 9 params from v1.0.0
	subspace.Set(ctx, v1consumertypes.KeyEnabled, true)
	subspace.Set(ctx, v1consumertypes.KeyBlocksPerDistributionTransmission, int64(10))
	subspace.Set(ctx, v1consumertypes.KeyDistributionTransmissionChannel, "channel-0")
	subspace.Set(ctx, v1consumertypes.KeyProviderFeePoolAddrStr, "cosmos17p3erf5gv2436fd4vyjwmudakts563a497syuz")
	subspace.Set(ctx, v1ccvtypes.KeyCCVTimeoutPeriod, time.Hour)
	subspace.Set(ctx, v1consumertypes.KeyTransferTimeoutPeriod, time.Hour)
	subspace.Set(ctx, v1consumertypes.KeyConsumerRedistributionFrac, "0.5")
	subspace.Set(ctx, v1consumertypes.KeyHistoricalEntries, int64(10))
	subspace.Set(ctx, v1consumertypes.KeyConsumerUnbondingPeriod, time.Hour)

	// Confirm 3 new params cannot be set with old key table
	require.Panics(t, func() {
		subspace.Set(ctx, v2consumertypes.KeySoftOptOutThreshold, "0.05")
	})
	require.Panics(t, func() {
		subspace.Set(ctx, v2consumertypes.KeyRewardDenoms, []string{"untrn"})
	})
	require.Panics(t, func() {
		subspace.Set(ctx, v2consumertypes.KeyProviderRewardDenoms, []string{"uatom"})
	})

	// Now create new subspace, mocking an upgrade where app initialization happens again
	subspace = paramtypes.NewSubspace(cdc,
		codec.NewLegacyAmino(),
		storeKey,
		memStoreKey,
		paramtypes.ModuleName,
	).WithKeyTable(v2consumertypes.ParamKeyTable()) // Use v2 key table, this would be set in keeper constructor upon app init

	// Run migration
	v2consumerkeeper.MigrateParamsv1Tov2(ctx, subspace)

	// Use v2 keeper to confirm params are set correctly
	keeper := v2consumerkeeper.Keeper{}
	keeper.SetParamSpace(ctx, subspace)

	params := keeper.GetParams(ctx)
	require.Equal(t, true, params.Enabled)
	require.Equal(t, int64(10), params.BlocksPerDistributionTransmission)
	require.Equal(t, "channel-0", params.DistributionTransmissionChannel)
	require.Equal(t, "cosmos17p3erf5gv2436fd4vyjwmudakts563a497syuz", params.ProviderFeePoolAddrStr)
	require.Equal(t, time.Hour, params.CcvTimeoutPeriod)
	require.Equal(t, time.Hour, params.TransferTimeoutPeriod)
	require.Equal(t, "0.5", params.ConsumerRedistributionFraction)
	require.Equal(t, int64(10), params.HistoricalEntries)
	require.Equal(t, time.Hour, params.UnbondingPeriod)
	// 3 new params are set to default values
	require.Equal(t, "0.05", params.SoftOptOutThreshold)
	require.Equal(t, []string(nil), params.RewardDenoms)
	require.Equal(t, []string(nil), params.ProviderRewardDenoms)

	// Set new params to other values
	params.SoftOptOutThreshold = "0.1"
	params.RewardDenoms = []string{"untrn"}
	params.ProviderRewardDenoms = []string{"uatom"}
	keeper.SetParams(ctx, params)

	require.Equal(t, "0.1", keeper.GetSoftOptOutThreshold(ctx))
	require.Equal(t, []string{"untrn"}, keeper.GetRewardDenoms(ctx))
	require.Equal(t, []string{"uatom"}, keeper.GetProviderRewardDenoms(ctx))
}
