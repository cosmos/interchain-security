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
	"github.com/cosmos/interchain-security/v2/testutil/crypto"
	testutil "github.com/cosmos/interchain-security/v2/testutil/keeper"
	consumertypes "github.com/cosmos/interchain-security/v2/x/ccv/consumer/types"
	providerkeeper "github.com/cosmos/interchain-security/v2/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/v2/x/ccv/provider/types"
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
	).WithKeyTable(v1KeyTable()) // Note that new param key table is set in keeper constructor

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
	).WithKeyTable(providertypes.ParamKeyTable()) // Use v2 key table, this would be set in keeper constructor upon app init

	// Run migration
	providerkeeper.MigrateParamsv1Tov2(ctx, subspace, sdk.NewCoin("uatom", sdk.NewInt(100000)))

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

	// Set new param to other values
	params.ConsumerRewardDenomRegistrationFee = sdk.NewCoin("uatom", sdk.NewInt(1000000000))
	keeper.SetParams(ctx, params)
	require.Equal(t, sdk.NewCoin("uatom", sdk.NewInt(1000000000)), keeper.GetParams(ctx).ConsumerRewardDenomRegistrationFee)
}

// v1KeyTable is a copy of the ParamKeyTable method from v1.0.0
func v1KeyTable() paramtypes.KeyTable {
	return paramtypes.NewKeyTable().RegisterParamSet(&v1Params{})
}

// ParamSetPairs implements params.ParamSet for v1Params
func (p *v1Params) ParamSetPairs() paramtypes.ParamSetPairs {
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

// v1Params is a copy of the Params struct from v1.0.0
type v1Params struct {
	TemplateClient              *types2.ClientState `protobuf:"bytes,1,opt,name=template_client,json=templateClient,proto3" json:"template_client,omitempty"`
	TrustingPeriodFraction      string              `protobuf:"bytes,2,opt,name=trusting_period_fraction,json=trustingPeriodFraction,proto3" json:"trusting_period_fraction,omitempty"`
	CcvTimeoutPeriod            time.Duration       `protobuf:"bytes,3,opt,name=ccv_timeout_period,json=ccvTimeoutPeriod,proto3,stdduration" json:"ccv_timeout_period"`
	InitTimeoutPeriod           time.Duration       `protobuf:"bytes,4,opt,name=init_timeout_period,json=initTimeoutPeriod,proto3,stdduration" json:"init_timeout_period"`
	VscTimeoutPeriod            time.Duration       `protobuf:"bytes,5,opt,name=vsc_timeout_period,json=vscTimeoutPeriod,proto3,stdduration" json:"vsc_timeout_period"`
	SlashMeterReplenishPeriod   time.Duration       `protobuf:"bytes,6,opt,name=slash_meter_replenish_period,json=slashMeterReplenishPeriod,proto3,stdduration" json:"slash_meter_replenish_period"`
	SlashMeterReplenishFraction string              `protobuf:"bytes,7,opt,name=slash_meter_replenish_fraction,json=slashMeterReplenishFraction,proto3" json:"slash_meter_replenish_fraction,omitempty"`
	MaxThrottledPackets         int64               `protobuf:"varint,8,opt,name=max_throttled_packets,json=maxThrottledPackets,proto3" json:"max_throttled_packets,omitempty"`
}

func TestMigrateConsumerGenesisv1Tov2(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testutil.GetProviderKeeperAndCtx(t, testutil.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	_, found := providerKeeper.GetConsumerGenesis(ctx, "neutron-1")
	require.False(t, found)

	providerKeeper.SetConsumerGenesis(ctx, "neutron-1", consumertypes.GenesisState{})

	_, found = providerKeeper.GetConsumerGenesis(ctx, "neutron-1")
	require.True(t, found)

	providerkeeper.MigrateConsumerGenesisStatesv1Tov2(ctx, providerKeeper)

	_, found = providerKeeper.GetConsumerGenesis(ctx, "neutron-1")
	require.False(t, found)
}

func TestMigrateKeysv1Tov2(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testutil.GetProviderKeeperAndCtx(t, testutil.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// First we setup a scenario that may show up in prod for v1,
	// where both slash logs and slash acks are persisted under the same key prefix
	cIds := crypto.GenMultipleCryptoIds(3, 349823489230)
	providerKeeper.SetSlashLogOnlyForTesting(ctx, cIds[0].SDKValConsAddress()) // This is the old (incorrect) method of storing slash logs
	providerKeeper.SetSlashLogOnlyForTesting(ctx, cIds[1].SDKValConsAddress())
	providerKeeper.SetSlashLogOnlyForTesting(ctx, cIds[2].SDKValConsAddress())

	// Setup slash acks
	p := []string{"alice", "bob", "frank"}
	providerKeeper.SetSlashAcks(ctx, "chain-1", p)
	p = []string{"charlie", "mac", "dennis"}
	providerKeeper.SetSlashAcks(ctx, "chain-2", p)

	// Mock two clients being established with chain-1 and chain-2,
	// This is needed for migration logic.
	providerKeeper.SetConsumerClientId(ctx, "chain-1", "client-1")
	providerKeeper.SetConsumerClientId(ctx, "chain-2", "client-2")

	// Confirm slash logs and slash acks exist together
	require.True(t, providerKeeper.GetSlashLogOnlyForTesting(ctx, cIds[0].SDKValConsAddress()))
	require.True(t, providerKeeper.GetSlashLogOnlyForTesting(ctx, cIds[1].SDKValConsAddress()))
	require.True(t, providerKeeper.GetSlashLogOnlyForTesting(ctx, cIds[2].SDKValConsAddress()))
	require.Len(t, providerKeeper.GetSlashAcks(ctx, "chain-1"), 3)
	require.Len(t, providerKeeper.GetSlashAcks(ctx, "chain-2"), 3)

	// Run migration
	providerkeeper.MigrateKeysv1Tov2(ctx, providerKeeper)

	// Confirm slash logs cannot be found from legacy methods
	require.False(t, providerKeeper.GetSlashLogOnlyForTesting(ctx, cIds[0].SDKValConsAddress()))
	require.False(t, providerKeeper.GetSlashLogOnlyForTesting(ctx, cIds[1].SDKValConsAddress()))
	require.False(t, providerKeeper.GetSlashLogOnlyForTesting(ctx, cIds[2].SDKValConsAddress()))

	// Slash acks remain unchanged
	require.Len(t, providerKeeper.GetSlashAcks(ctx, "chain-1"), 3)
	require.Len(t, providerKeeper.GetSlashAcks(ctx, "chain-2"), 3)

	// Confirm slash logs can be found from new/correct methods
	require.True(t, providerKeeper.GetSlashLog(ctx, cIds[0].ProviderConsAddress()))
	require.True(t, providerKeeper.GetSlashLog(ctx, cIds[1].ProviderConsAddress()))
	require.True(t, providerKeeper.GetSlashLog(ctx, cIds[2].ProviderConsAddress()))
}
