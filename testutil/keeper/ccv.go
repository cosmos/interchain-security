package keeper

// import (
// 	"testing"

// 	sdk "github.com/cosmos/cosmos-sdk/types"
// 	"github.com/cosmos/interchain-security/x/ccv/consumer/keeper"
// )

// func CcvKeeper(t testing.TB) (*keeper.Keeper, sdk.Context) {
// 	// storeKey := sdk.NewKVStoreKey(types.StoreKey)
// 	// memStoreKey := storetypes.NewMemoryStoreKey(types.MemStoreKey)

// 	// db := tmdb.NewMemDB()
// 	// stateStore := store.NewCommitMultiStore(db)
// 	// stateStore.MountStoreWithDB(storeKey, sdk.StoreTypeIAVL, db)
// 	// stateStore.MountStoreWithDB(memStoreKey, sdk.StoreTypeMemory, nil)
// 	// require.NoError(t, stateStore.LoadLatestVersion())

// 	// registry := codectypes.NewInterfaceRegistry()
// 	// k := keeper.NewKeeper(
// 	// 	codec.NewProtoCodec(registry),
// 	// 	storeKey,
// 	// 	memStoreKey,
// 	// )

// 	// ctx := sdk.NewContext(stateStore, tmproto.Header{}, false, log.NewNopLogger())
// 	// return k, ctx
// }
