package keeper

import (
	"testing"

	"github.com/cosmos/cosmos-sdk/codec"
	codectypes "github.com/cosmos/cosmos-sdk/codec/types"
	"github.com/cosmos/cosmos-sdk/store"
	storetypes "github.com/cosmos/cosmos-sdk/store/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	capabilitykeeper "github.com/cosmos/cosmos-sdk/x/capability/keeper"
	paramstypes "github.com/cosmos/cosmos-sdk/x/params/types"
	consumerkeeper "github.com/cosmos/interchain-security/x/ccv/consumer/keeper"
	providerkeeper "github.com/cosmos/interchain-security/x/ccv/provider/keeper"
	"github.com/cosmos/interchain-security/x/ccv/types"
	"github.com/stretchr/testify/require"
	"github.com/tendermint/tendermint/libs/log"
	tmproto "github.com/tendermint/tendermint/proto/tendermint/types"
	tmdb "github.com/tendermint/tm-db"
)

// Constructs a provider keeper and context object for unit tests, backed by an in-memory db.
func GetProviderKeeperAndCtx(t testing.TB) (providerkeeper.Keeper, sdk.Context) {

	cdc, storeKey, paramsSubspace, ctx := SetupInMemKeeper(t)

	k := providerkeeper.NewKeeper(
		cdc,
		storeKey,
		paramsSubspace,
		&MockScopedKeeper{},
		&MockChannelKeeper{},
		&MockPortKeeper{},
		&MockConnectionKeeper{},
		&MockClientKeeper{},
		&MockStakingKeeper{},
		&MockSlashingKeeper{},
		&MockAccountKeeper{},
		"",
	)
	return k, ctx
}

// Constructs a consumer keeper and context object for unit tests, backed by an in-memory db.
func GetConsumerKeeperAndCtx(t testing.TB) (consumerkeeper.Keeper, sdk.Context) {

	cdc, storeKey, paramsSubspace, ctx := SetupInMemKeeper(t)

	k := consumerkeeper.NewKeeper(
		cdc,
		storeKey,
		paramsSubspace,
		&MockScopedKeeper{},
		&MockChannelKeeper{},
		&MockPortKeeper{},
		&MockConnectionKeeper{},
		&MockClientKeeper{},
		&MockSlashingKeeper{},
		&MockBankKeeper{},
		&MockAccountKeeper{},
		&MockIBCTransferKeeper{},
		&MockIBCCoreKeeper{},
		"",
	)
	return k, ctx
}

// Constructs a provider keeper for unit tests, backed by an in-memory db,
// with ability to pass mocked or otherwise manipulated parameters.
func GetProviderKeeperWithMocks(t testing.TB,
	cdc *codec.ProtoCodec,
	storeKey *storetypes.KVStoreKey,
	paramsSubspace paramstypes.Subspace,
	capabilityKeeper capabilitykeeper.ScopedKeeper,
	channelKeeper types.ChannelKeeper,
	portKeeper types.PortKeeper,
	connectionKeeper types.ConnectionKeeper,
	clientKeeper types.ClientKeeper,
	stakingKeeper types.StakingKeeper,
	slashingKeeper types.SlashingKeeper,
	accountKeeper types.AccountKeeper,
) providerkeeper.Keeper {

	k := providerkeeper.NewKeeper(
		cdc,
		storeKey,
		paramsSubspace,
		capabilityKeeper,
		channelKeeper,
		portKeeper,
		connectionKeeper,
		clientKeeper,
		stakingKeeper,
		slashingKeeper,
		accountKeeper,
		"",
	)
	return k
}

// Constructs a consumer keeper for unit tests, backed by an in-memory db,
// with ability to pass mocked or otherwise manipulated parameters.
func GetConsumerKeeperWithMocks(t testing.TB,
	cdc *codec.ProtoCodec,
	storeKey *storetypes.KVStoreKey,
	paramsSubspace paramstypes.Subspace,
	capabilityKeeper types.ScopedKeeper,
	channelKeeper types.ChannelKeeper,
	portKeeper types.PortKeeper,
	connectionKeeper types.ConnectionKeeper,
	clientKeeper types.ClientKeeper,
	slashingKeeper types.SlashingKeeper,
	bankKeeper types.BankKeeper,
	accountKeeper types.AccountKeeper,
	ibcTransferKeeper types.IBCTransferKeeper,
	ibcCoreKeeper types.IBCCoreKeeper,
) consumerkeeper.Keeper {

	k := consumerkeeper.NewKeeper(
		cdc,
		storeKey,
		paramsSubspace,
		capabilityKeeper,
		channelKeeper,
		portKeeper,
		connectionKeeper,
		clientKeeper,
		slashingKeeper,
		bankKeeper,
		accountKeeper,
		ibcTransferKeeper,
		ibcCoreKeeper,
		"",
	)
	return k
}

func SetupInMemKeeper(t testing.TB) (*codec.ProtoCodec, *storetypes.KVStoreKey, paramstypes.Subspace, sdk.Context) {
	storeKey := sdk.NewKVStoreKey(types.StoreKey)
	memStoreKey := storetypes.NewMemoryStoreKey(types.MemStoreKey)

	db := tmdb.NewMemDB()
	stateStore := store.NewCommitMultiStore(db)
	stateStore.MountStoreWithDB(storeKey, sdk.StoreTypeIAVL, db)
	stateStore.MountStoreWithDB(memStoreKey, sdk.StoreTypeMemory, nil)
	require.NoError(t, stateStore.LoadLatestVersion())

	registry := codectypes.NewInterfaceRegistry()
	cdc := codec.NewProtoCodec(registry)

	paramsSubspace := paramstypes.NewSubspace(cdc,
		codec.NewLegacyAmino(),
		storeKey,
		memStoreKey,
		paramstypes.ModuleName,
	)
	ctx := sdk.NewContext(stateStore, tmproto.Header{}, false, log.NewNopLogger())
	return cdc, storeKey, paramsSubspace, ctx
}
