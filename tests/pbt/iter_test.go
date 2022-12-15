package pbt_test

import (
	"testing"

	sdk "github.com/cosmos/cosmos-sdk/types"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	"github.com/cosmos/interchain-security/x/ccv/provider/keeper"
	"github.com/golang/mock/gomock"
	"pgregory.net/rapid"
)

///////////////////////////////////////////////////////////////
// SYSTEM UNDER TEST
///////////////////////////////////////////////////////////////

type Wiz struct {
	pk   keeper.Keeper
	ctx  sdk.Context
	ctrl *gomock.Controller
}

func NewWiz(t *testing.T) *Wiz {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	return &Wiz{
		pk:   providerKeeper,
		ctx:  ctx,
		ctrl: ctrl,
	}
}

func (w *Wiz) Cleanup() {
	w.ctrl.Finish()
}

func (w *Wiz) Pop() {
}

///////////////////////////////////////////////////////////////
// TESTING CODE
///////////////////////////////////////////////////////////////

type IterHarness struct {
	wiz *Wiz // Wiz being tested
}

// Init is an action for initializing  a WizMachine instance.
func (h *IterHarness) Init(t *rapid.T) {
}

func (h *IterHarness) Cleanup(t *rapid.T) {
	h.wiz.Cleanup()
}

// Check runs after every action and verifies that all required invariants hold.
func (h *IterHarness) Check(t *rapid.T) {
}

func TestWiz(t *testing.T) {
	rapid.Check(t, rapid.Run[*IterHarness]())
}
