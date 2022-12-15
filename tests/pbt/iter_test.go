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

func NewInMemKeeperParams() testkeeper.InMemKeeperParams {
	storeKey := sdk.NewKVStoreKey(types.StoreKey)
	memStoreKey := storetypes.NewMemoryStoreKey(types.MemStoreKey)

	db := tmdb.NewMemDB()
	stateStore := store.NewCommitMultiStore(db)
	stateStore.MountStoreWithDB(storeKey, sdk.StoreTypeIAVL, db)
	stateStore.MountStoreWithDB(memStoreKey, sdk.StoreTypeMemory, nil)

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

type Wiz struct {
	pk   keeper.Keeper
	ctx  sdk.Context
	ctrl *gomock.Controller
}

func NewWiz(t *rapid.T) *Wiz {
	providerKeeper, ctx, ctrl, _ := GetProviderKeeperAndCtx(t, NewInMemKeeperParams())
	return &Wiz{
		pk:   providerKeeper,
		ctx:  ctx,
		ctrl: ctrl,
	}
}

func (w *Wiz) Cleanup() {
	w.ctrl.Finish()
}

func (w *Wiz) Set(k, v string) {
	w.pk.SetChainToChannel(w.ctx, k, v)
}
func (w *Wiz) Get(k string) (string, bool) {
	return w.pk.GetChainToChannel(w.ctx, k)
}
func (w *Wiz) Del(k string) {
	w.pk.DeleteChainToChannel(w.ctx, k)
}
func (w *Wiz) Iter() []string {
	ret := []string{}
	w.pk.IterateConsumerChains(w.ctx, func(_ sdk.Context, k string, v string) bool {
		ret = append(ret, k)
		return false
	})
	return ret
}

///////////////////////////////////////////////////////////////
// TESTING CODE
///////////////////////////////////////////////////////////////

type IterHarness struct {
	wiz   *Wiz // Wiz being tested
	model map[string]string
}

// Init is an action for initializing  a WizMachine instance.
func (h *IterHarness) Init(t *rapid.T) {
	h.wiz = NewWiz(t)
	h.model = map[string]string{}
}

func (h *IterHarness) Cleanup(t *rapid.T) {
	h.wiz.Cleanup()
}

func (h *IterHarness) Set(k, v string) {
	h.wiz.Set(k, v)
	h.model[k] = v
}
func (h *IterHarness) Get(k string) string {
	expect, expectOk := h.model[k]
	actual, actualOk := h.wiz.Get(k)
	require.Equal(t, expectOk, actualOk)
	if expectOk {
		require.Equal(t, expect, actual)
	}
}
func (h *IterHarness) Del(k string) {
}
func (h *IterHarness) Iter() []string {
}

// Check runs after every action and verifies that all required invariants hold.
func (h *IterHarness) Check(t *rapid.T) {
	// t.Helper().Log("Check")
}

func TestWiz(t *testing.T) {
	rapid.Check(t, rapid.Run[*IterHarness]())
}
