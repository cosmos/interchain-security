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
	consumerkeeper "github.com/cosmos/interchain-security/x/ccv/consumer/keeper"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"
	"github.com/stretchr/testify/require"
	"github.com/tendermint/tendermint/libs/log"
	tmproto "github.com/tendermint/tendermint/proto/tendermint/types"
	tmdb "github.com/tendermint/tm-db"
)

func TestMigrateParamsv1p0To1p3(t *testing.T) {
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
	subspace = subspace.WithKeyTable(consumertypes.ParamKeyTable())

	// Set 9 params from v1.0.0
	subspace.Set(ctx, consumertypes.KeyEnabled, true)
	subspace.Set(ctx, consumertypes.KeyBlocksPerDistributionTransmission, int64(10))
	subspace.Set(ctx, consumertypes.KeyDistributionTransmissionChannel, "channel-0")
	subspace.Set(ctx, consumertypes.KeyProviderFeePoolAddrStr, "cosmos17p3erf5gv2436fd4vyjwmudakts563a497syuz")
	subspace.Set(ctx, ccvtypes.KeyCCVTimeoutPeriod, time.Hour)
	subspace.Set(ctx, consumertypes.KeyTransferTimeoutPeriod, time.Hour)
	subspace.Set(ctx, consumertypes.KeyConsumerRedistributionFrac, "0.5")
	subspace.Set(ctx, consumertypes.KeyHistoricalEntries, int64(10))
	subspace.Set(ctx, consumertypes.KeyConsumerUnbondingPeriod, time.Hour)

	// Confirm 3 new params are not set
	require.False(t, subspace.Has(ctx, consumertypes.KeySoftOptOutThreshold))
	require.False(t, subspace.Has(ctx, consumertypes.KeyRewardDenoms))
	require.False(t, subspace.Has(ctx, consumertypes.KeyProviderRewardDenoms))

	// Run migration
	consumerkeeper.MigrateParamsv1p0To1p3(ctx, subspace)

	// Use keeper to confirm params are set correctly
	keeper := consumerkeeper.Keeper{}
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
