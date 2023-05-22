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
	types2 "github.com/cosmos/ibc-go/v4/modules/light-clients/07-tendermint/types"
	providerkeeper "github.com/cosmos/interchain-security/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
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
	subspace = subspace.WithKeyTable(v1p0p0KeyTable())

	// Set 8 params from v1.0.0
	subspace.Set(ctx, providertypes.KeyTemplateClient, providertypes.DefaultParams().TemplateClient)
	subspace.Set(ctx, providertypes.KeyTrustingPeriodFraction, "0.75")
	subspace.Set(ctx, ccvtypes.KeyCCVTimeoutPeriod, time.Hour)
	subspace.Set(ctx, providertypes.KeyInitTimeoutPeriod, time.Hour)
	subspace.Set(ctx, providertypes.KeyVscTimeoutPeriod, time.Hour)
	subspace.Set(ctx, providertypes.KeySlashMeterReplenishPeriod, time.Hour)
	subspace.Set(ctx, providertypes.KeySlashMeterReplenishFraction, "0.5")
	subspace.Set(ctx, providertypes.KeyMaxThrottledPackets, int64(10))

	// Confirm new param cannot be set with old key table
	require.Panics(t, func() {
		subspace.Set(ctx, providertypes.KeyConsumerRewardDenomRegistrationFee, sdk.NewInt64Coin("uatom", 100))
	})

	// Now create new subspace, mocking an upgrade where app initialization happens again
	subspace = paramtypes.NewSubspace(cdc,
		codec.NewLegacyAmino(),
		storeKey,
		memStoreKey,
		paramtypes.ModuleName,
	).WithKeyTable(providertypes.ParamKeyTable()) // Use new key table, this would be set in keeper constructor

	// Run migration
	providerkeeper.MigrateParamsv1p0To1p3(ctx, subspace, sdk.NewCoin("uatom", sdk.NewInt(100000)))

	// Use keeper to confirm params are set correctly
	keeper := providerkeeper.Keeper{}
	keeper.SetParamSpace(ctx, subspace)

	params := keeper.GetParams(ctx)
	require.Equal(t, providertypes.DefaultParams().TemplateClient, params.TemplateClient)
	require.Equal(t, "0.75", params.TrustingPeriodFraction)
	require.Equal(t, time.Hour, params.CcvTimeoutPeriod)
	require.Equal(t, time.Hour, params.InitTimeoutPeriod)
	require.Equal(t, time.Hour, params.VscTimeoutPeriod)
	require.Equal(t, time.Hour, params.SlashMeterReplenishPeriod)
	require.Equal(t, "0.5", params.SlashMeterReplenishFraction)
	require.Equal(t, int64(10), params.MaxThrottledPackets)
	// New param should be set
	require.Equal(t, sdk.NewCoin("uatom", sdk.NewInt(100000)), params.ConsumerRewardDenomRegistrationFee)

	// Set new params to other values
	params.ConsumerRewardDenomRegistrationFee = sdk.NewCoin("uatom", sdk.NewInt(1000000000))
	keeper.SetParams(ctx, params)
	require.Equal(t, sdk.NewCoin("uatom", sdk.NewInt(1000000000)), keeper.GetParams(ctx).ConsumerRewardDenomRegistrationFee)
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
		paramtypes.NewParamSetPair(providertypes.KeyTemplateClient, p.TemplateClient, providertypes.ValidateTemplateClient),
		paramtypes.NewParamSetPair(providertypes.KeyTrustingPeriodFraction, p.TrustingPeriodFraction, ccvtypes.ValidateStringFraction),
		paramtypes.NewParamSetPair(ccvtypes.KeyCCVTimeoutPeriod, p.CcvTimeoutPeriod, ccvtypes.ValidateDuration),
		paramtypes.NewParamSetPair(providertypes.KeyInitTimeoutPeriod, p.InitTimeoutPeriod, ccvtypes.ValidateDuration),
		paramtypes.NewParamSetPair(providertypes.KeyVscTimeoutPeriod, p.VscTimeoutPeriod, ccvtypes.ValidateDuration),
		paramtypes.NewParamSetPair(providertypes.KeySlashMeterReplenishPeriod, p.SlashMeterReplenishPeriod, ccvtypes.ValidateDuration),
		paramtypes.NewParamSetPair(providertypes.KeySlashMeterReplenishFraction, p.SlashMeterReplenishFraction, ccvtypes.ValidateStringFraction),
		paramtypes.NewParamSetPair(providertypes.KeyMaxThrottledPackets, p.MaxThrottledPackets, ccvtypes.ValidatePositiveInt64),
	}
}

// v1p0p0Params is a copy of the Params struct from v1.0.0
type v1p0p0Params struct {
	TemplateClient              *types2.ClientState `protobuf:"bytes,1,opt,name=template_client,json=templateClient,proto3" json:"template_client,omitempty"`
	TrustingPeriodFraction      string              `protobuf:"bytes,2,opt,name=trusting_period_fraction,json=trustingPeriodFraction,proto3" json:"trusting_period_fraction,omitempty"`
	CcvTimeoutPeriod            time.Duration       `protobuf:"bytes,3,opt,name=ccv_timeout_period,json=ccvTimeoutPeriod,proto3,stdduration" json:"ccv_timeout_period"`
	InitTimeoutPeriod           time.Duration       `protobuf:"bytes,4,opt,name=init_timeout_period,json=initTimeoutPeriod,proto3,stdduration" json:"init_timeout_period"`
	VscTimeoutPeriod            time.Duration       `protobuf:"bytes,5,opt,name=vsc_timeout_period,json=vscTimeoutPeriod,proto3,stdduration" json:"vsc_timeout_period"`
	SlashMeterReplenishPeriod   time.Duration       `protobuf:"bytes,6,opt,name=slash_meter_replenish_period,json=slashMeterReplenishPeriod,proto3,stdduration" json:"slash_meter_replenish_period"`
	SlashMeterReplenishFraction string              `protobuf:"bytes,7,opt,name=slash_meter_replenish_fraction,json=slashMeterReplenishFraction,proto3" json:"slash_meter_replenish_fraction,omitempty"`
	MaxThrottledPackets         int64               `protobuf:"varint,8,opt,name=max_throttled_packets,json=maxThrottledPackets,proto3" json:"max_throttled_packets,omitempty"`
}
