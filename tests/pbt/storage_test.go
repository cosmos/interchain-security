package pbt_test

import (
	"testing"

	"github.com/cosmos/cosmos-sdk/codec"
	codectypes "github.com/cosmos/cosmos-sdk/codec/types"
	"github.com/cosmos/cosmos-sdk/store"
	storetypes "github.com/cosmos/cosmos-sdk/store/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	paramstypes "github.com/cosmos/cosmos-sdk/x/params/types"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	"github.com/cosmos/interchain-security/x/ccv/provider/keeper"
	"github.com/cosmos/interchain-security/x/ccv/types"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"
	"github.com/tendermint/tendermint/libs/log"
	tmproto "github.com/tendermint/tendermint/proto/tendermint/types"
	tmdb "github.com/tendermint/tm-db"
	"pgregory.net/rapid"
)

///////////////////////////////////////////////////////////////
// HACKY STUFF TO GET MOCKS WITH rapid.T
///////////////////////////////////////////////////////////////

func GetProviderKeeperAndCtx(t *rapid.T, params testkeeper.InMemKeeperParams) (
	keeper.Keeper, sdk.Context, *gomock.Controller, testkeeper.MockedKeepers) {
	ctrl := gomock.NewController(t)
	mocks := testkeeper.NewMockedKeepers(ctrl)
	return testkeeper.NewInMemProviderKeeper(params, mocks), params.Ctx, ctrl, mocks
}

func NewInMemKeeperParams(t *rapid.T) testkeeper.InMemKeeperParams {
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

	return testkeeper.InMemKeeperParams{
		Cdc:            cdc,
		StoreKey:       storeKey,
		ParamsSubspace: &paramsSubspace,
		Ctx:            ctx,
	}
}

///////////////////////////////////////////////////////////////
// SYSTEM UNDER TEST
///////////////////////////////////////////////////////////////

type StoredThing struct {
	pk   keeper.Keeper
	ctx  sdk.Context
	ctrl *gomock.Controller
}

func (w *StoredThing) Set(k, v string) {
	w.pk.SetChainToChannel(w.ctx, k, v)
}

func (w *StoredThing) Get(k string) (string, bool) {
	return w.pk.GetChainToChannel(w.ctx, k)
}

func (w *StoredThing) Del(k string) {
	w.pk.DeleteChainToChannel(w.ctx, k)
}

func (w *StoredThing) Iter(n int) []string {
	ret := []string{}
	cnt := 0
	w.pk.IterateConsumerChains(w.ctx, func(_ sdk.Context, k string, v string) bool {
		ret = append(ret, k)
		cnt += 1
		return n <= cnt
	})
	return ret
}

///////////////////////////////////////////////////////////////
// TESTING CODE
///////////////////////////////////////////////////////////////

type StoreHarness struct {
	wiz   *StoredThing // Wiz being tested
	model map[string]string
}

// Init is an action for initializing  a WizMachine instance.
func (h *StoreHarness) Init(t *rapid.T) {
	providerKeeper, ctx, ctrl, _ := GetProviderKeeperAndCtx(t, NewInMemKeeperParams(t))
	h.wiz = &StoredThing{
		pk:   providerKeeper,
		ctx:  ctx,
		ctrl: ctrl,
	}
	h.model = map[string]string{}
}

func (h *StoreHarness) Cleanup() {
	h.wiz.ctrl.Finish()
}

func (h *StoreHarness) Set(t *rapid.T) {
	k := rapid.String().Draw(t, "k")
	v := rapid.String().Draw(t, "v")
	h.wiz.Set(k, v)
	h.model[k] = v
}

func (h *StoreHarness) Del(t *rapid.T) {
	k := rapid.String().Draw(t, "k")
	h.wiz.Del(k)
	delete(h.model, k)
}

// Check runs after each action
func (h *StoreHarness) Check(t *rapid.T) {

	get := func() {
		k := rapid.String().Draw(t, "k")
		expect, expectOk := h.model[k]
		actual, actualOk := h.wiz.Get(k)
		require.Equal(t, expectOk, actualOk)
		// Exercise: do you think it's a good to check the value is equal
		// even if it was not expected to be found?
		if expectOk {
			require.Equal(t, expect, actual)
		}
	}

	iter := func() {
		// Exercise, how would this function (and the rest of code) need
		// to change if we were testing data which was supposed to be
		// sorted?
		n := rapid.IntRange(0, 100).Draw(t, "n")
		iterated := h.wiz.Iter(n)
		if len(h.model) < n {
			n = len(h.model)
		}
		require.Len(t, iterated, n)
		for _, s := range iterated {
			_, ok := h.model[s]
			require.True(t, ok)
		}
	}

	get()
	iter()
}

func TestWiz(t *testing.T) {
	rapid.Check(t, rapid.Run[*StoreHarness]())
}
