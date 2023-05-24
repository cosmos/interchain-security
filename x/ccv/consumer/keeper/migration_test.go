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
	consumerkeeper "github.com/cosmos/interchain-security/v2/x/ccv/consumer/keeper"
	consumertypes "github.com/cosmos/interchain-security/v2/x/ccv/consumer/types"
	ccvtypes "github.com/cosmos/interchain-security/v2/x/ccv/types"
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
	subspace = subspace.WithKeyTable(v1p0p0KeyTable())

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

	// Confirm 3 new params cannot be set with old key table
	require.Panics(t, func() {
		subspace.Set(ctx, consumertypes.KeySoftOptOutThreshold, "0.05")
	})
	require.Panics(t, func() {
		subspace.Set(ctx, consumertypes.KeyRewardDenoms, []string{"untrn"})
	})
	require.Panics(t, func() {
		subspace.Set(ctx, consumertypes.KeyProviderRewardDenoms, []string{"uatom"})
	})

	// Now create new subspace, mocking an upgrade where app initialization happens again
	subspace = paramtypes.NewSubspace(cdc,
		codec.NewLegacyAmino(),
		storeKey,
		memStoreKey,
		paramtypes.ModuleName,
	).WithKeyTable(consumertypes.ParamKeyTable()) // Use v2 key table, this would be set in keeper constructor upon app init

	// Run migration
	consumerkeeper.MigrateParamsv1Tov2(ctx, subspace)

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

//
// Note: the following methods and struct could be removed if v1.3.0 is actually defined as v2.0.0
// and we bump the go.mod package name accordingly
//

// v1p0p0Params is a copy of the ParamKeyTable method from v1.0.0
func v1p0p0KeyTable() paramtypes.KeyTable {
	return paramtypes.NewKeyTable().RegisterParamSet(&v1p0p0Params{})
}

// ParamSetPairs implements params.ParamSet for v1p0p0Params
func (p *v1p0p0Params) ParamSetPairs() paramtypes.ParamSetPairs {
	return paramtypes.ParamSetPairs{
		paramtypes.NewParamSetPair(consumertypes.KeyEnabled, p.Enabled, ccvtypes.ValidateBool),
		paramtypes.NewParamSetPair(consumertypes.KeyBlocksPerDistributionTransmission,
			p.BlocksPerDistributionTransmission, ccvtypes.ValidatePositiveInt64),
		paramtypes.NewParamSetPair(consumertypes.KeyDistributionTransmissionChannel,
			p.DistributionTransmissionChannel, consumertypes.ValidateDistributionTransmissionChannel),
		paramtypes.NewParamSetPair(consumertypes.KeyProviderFeePoolAddrStr,
			p.ProviderFeePoolAddrStr, consumertypes.ValidateProviderFeePoolAddrStr),
		paramtypes.NewParamSetPair(ccvtypes.KeyCCVTimeoutPeriod,
			p.CcvTimeoutPeriod, ccvtypes.ValidateDuration),
		paramtypes.NewParamSetPair(consumertypes.KeyTransferTimeoutPeriod,
			p.TransferTimeoutPeriod, ccvtypes.ValidateDuration),
		paramtypes.NewParamSetPair(consumertypes.KeyConsumerRedistributionFrac,
			p.ConsumerRedistributionFraction, ccvtypes.ValidateStringFraction),
		paramtypes.NewParamSetPair(consumertypes.KeyHistoricalEntries,
			p.HistoricalEntries, ccvtypes.ValidatePositiveInt64),
		paramtypes.NewParamSetPair(consumertypes.KeyConsumerUnbondingPeriod,
			p.UnbondingPeriod, ccvtypes.ValidateDuration),
	}
}

// v1p0p0Params is a copy of the Params struct from v1.0.0
type v1p0p0Params struct {
	Enabled                           bool          `protobuf:"varint,1,opt,name=enabled,proto3" json:"enabled,omitempty"`
	BlocksPerDistributionTransmission int64         `protobuf:"varint,2,opt,name=blocks_per_distribution_transmission,json=blocksPerDistributionTransmission,proto3" json:"blocks_per_distribution_transmission,omitempty"`
	DistributionTransmissionChannel   string        `protobuf:"bytes,3,opt,name=distribution_transmission_channel,json=distributionTransmissionChannel,proto3" json:"distribution_transmission_channel,omitempty"`
	ProviderFeePoolAddrStr            string        `protobuf:"bytes,4,opt,name=provider_fee_pool_addr_str,json=providerFeePoolAddrStr,proto3" json:"provider_fee_pool_addr_str,omitempty"`
	CcvTimeoutPeriod                  time.Duration `protobuf:"bytes,5,opt,name=ccv_timeout_period,json=ccvTimeoutPeriod,proto3,stdduration" json:"ccv_timeout_period"`
	TransferTimeoutPeriod             time.Duration `protobuf:"bytes,6,opt,name=transfer_timeout_period,json=transferTimeoutPeriod,proto3,stdduration" json:"transfer_timeout_period"`
	ConsumerRedistributionFraction    string        `protobuf:"bytes,7,opt,name=consumer_redistribution_fraction,json=consumerRedistributionFraction,proto3" json:"consumer_redistribution_fraction,omitempty"`
	HistoricalEntries                 int64         `protobuf:"varint,8,opt,name=historical_entries,json=historicalEntries,proto3" json:"historical_entries,omitempty"`
	UnbondingPeriod                   time.Duration `protobuf:"bytes,9,opt,name=unbonding_period,json=unbondingPeriod,proto3,stdduration" json:"unbonding_period"`
}
