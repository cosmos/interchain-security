package difftest_test

import (
	"math/big"
	"testing"
	"time"

	"github.com/cosmos/cosmos-sdk/codec"
	cryptotypes "github.com/cosmos/cosmos-sdk/crypto/types"
	"github.com/cosmos/cosmos-sdk/simapp"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/x/staking"
	"github.com/cosmos/cosmos-sdk/x/staking/keeper"
	"github.com/cosmos/cosmos-sdk/x/staking/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	"github.com/stretchr/testify/require"
	tmproto "github.com/tendermint/tendermint/proto/tendermint/types"
)

func init() {
	sdk.DefaultPowerReduction = sdk.NewIntFromBigInt(new(big.Int).Exp(big.NewInt(10), big.NewInt(18), nil))
}

const (
	v0 = "v0"
	d0 = "d0"
	d1 = "d1"
	d2 = "d2"
)

var (
	PKs = simapp.CreateTestPubKeys(500)
)

func scaledAmt(modelAmt int) sdk.Int {
	return sdk.TokensFromConsensusPower(int64(modelAmt), sdk.DefaultPowerReduction)
}

// constructs a  rates with all zeros.
func zeroCommission() stakingtypes.CommissionRates {
	return stakingtypes.NewCommissionRates(sdk.ZeroDec(), sdk.ZeroDec(), sdk.ZeroDec())
}

func getBaseSimappWithCustomKeeper() (*codec.LegacyAmino, *simapp.SimApp, sdk.Context) {
	app := simapp.Setup(false)
	ctx := app.BaseApp.NewContext(false, tmproto.Header{})

	appCodec := app.AppCodec()

	app.StakingKeeper = keeper.NewKeeper(
		appCodec,
		app.GetKey(types.StoreKey),
		app.GetTKey(types.TStoreKey),
		app.AccountKeeper,
		app.BankKeeper,
		app.GetSubspace(types.ModuleName),
	)
	app.StakingKeeper.SetParams(ctx, types.DefaultParams())

	return codec.NewLegacyAmino(), app, ctx
}

func generateAddresses(app *simapp.SimApp, ctx sdk.Context, numAddrs int, accAmount sdk.Int) ([]sdk.AccAddress, []sdk.ValAddress) {
	addrDels := simapp.AddTestAddrsIncremental(app, ctx, numAddrs, accAmount)
	addrVals := simapp.ConvertAddrsToValAddrs(addrDels)

	return addrDels, addrVals
}

func bootstrapHandlerGenesisTest(t *testing.T, power int64, numAddrs int, accAmount sdk.Int) (*simapp.SimApp, sdk.Context, []sdk.AccAddress, []sdk.ValAddress) {
	_, app, ctx := getBaseSimappWithCustomKeeper()

	addrDels, addrVals := generateAddresses(app, ctx, numAddrs, accAmount)

	amt := app.StakingKeeper.TokensFromConsensusPower(ctx, power)
	totalSupply := sdk.NewCoins(sdk.NewCoin(app.StakingKeeper.BondDenom(ctx), amt.MulRaw(int64(len(addrDels)))))

	notBondedPool := app.StakingKeeper.GetNotBondedPool(ctx)

	// set non bonded pool balance
	app.AccountKeeper.SetModuleAccount(ctx, notBondedPool)
	require.NoError(t, simapp.FundModuleAccount(app.BankKeeper, ctx, notBondedPool.GetName(), totalSupply))
	return app, ctx, addrDels, addrVals
}

type helperx struct {
	t     *testing.T
	h     sdk.Handler
	k     keeper.Keeper
	bk    types.BankKeeper
	ctx   sdk.Context
	denom string
}

func newHelperx(t *testing.T, ctx sdk.Context, k keeper.Keeper, bk types.BankKeeper) *helperx {
	return &helperx{t, staking.NewHandler(k), k, bk, ctx, sdk.DefaultBondDenom}
}

// handle calls staking handler on a given message
func (h *helperx) handle(msg sdk.Msg, ok bool) *sdk.Result {
	res, err := h.h(h.ctx, msg)
	if ok {
		require.NoError(h.t, err)
		require.NotNil(h.t, res)
	} else {
		require.Error(h.t, err)
		require.Nil(h.t, res)
	}
	return res
}

func (h *helperx) createValidator(addr sdk.ValAddress, pk cryptotypes.PubKey, stakeAmt int, ok bool) {
	coin := sdk.NewCoin(h.denom, scaledAmt(stakeAmt))
	msg, err := stakingtypes.NewMsgCreateValidator(addr, pk, coin, stakingtypes.Description{}, zeroCommission(), sdk.ZeroInt())
	require.NoError(h.t, err)
	h.handle(msg, ok)
}

func (h *helperx) delegate(delegator sdk.AccAddress, val sdk.ValAddress, amt int, ok bool) {
	coin := sdk.NewCoin(h.denom, scaledAmt(amt))
	msg := stakingtypes.NewMsgDelegate(delegator, val, coin)
	h.handle(msg, ok)
}

func (h *helperx) undelegate(delegator sdk.AccAddress, val sdk.ValAddress, amt int, ok bool) *sdk.Result {
	coin := sdk.NewCoin(h.denom, scaledAmt(amt))
	msg := stakingtypes.NewMsgUndelegate(delegator, val, coin)
	return h.handle(msg, ok)
}

func (h *helperx) beginRedelegate(delegator sdk.AccAddress, src sdk.ValAddress, dst sdk.ValAddress, amt int, ok bool) *sdk.Result {
	coin := sdk.NewCoin(h.denom, scaledAmt(amt))
	msg := stakingtypes.NewMsgBeginRedelegate(delegator, src, dst, coin)
	return h.handle(msg, ok)
}

func (h *helperx) slash(val sdk.ValAddress, height int64, power int64, factor sdk.Dec) {
	cons := sdk.ConsAddress(val)
	h.k.Slash(h.ctx, cons, height, power, factor, -1)
}

func (h *helperx) matchValidatorStatus(val sdk.ValAddress, status string) {
	validator, _ := h.k.GetValidator(h.ctx, val)
	actual := validator.GetStatus()
	if status == "bonded" {
		require.Equalf(h.t, types.Bonded, actual, "exp: %s ", status)
	}
	if status == "unbonding" {
		require.Equalf(h.t, types.Unbonding, actual, "exp: %s ", status)
	}
	if status == "unbonded" {
		require.Equalf(h.t, types.Unbonded, actual, "exp: %s ", status)
	}
}

func (h *helperx) matchBalance(addr sdk.AccAddress, amt int) {
	bal := h.bk.GetBalance(h.ctx, addr, h.denom)
	exp := sdk.NewCoin(h.denom, scaledAmt(amt))
	require.Equal(h.t, exp, bal)
}

func Adversarial(t *testing.T) {
	ix := make(map[string]int)
	ix[v0] = 0
	ix[d0] = 1
	ix[d1] = 2
	ix[d2] = 3

	initPower := int64(0)
	numAddresses := 4
	app, ctx, delAddrs, valAddrs := bootstrapHandlerGenesisTest(t, initPower, numAddresses, sdk.TokensFromConsensusPower(initPower, sdk.DefaultPowerReduction))
	validators, delegators := valAddrs[:1], delAddrs

	params := app.StakingKeeper.GetParams(ctx)
	params.UnbondingTime = 2 * time.Second
	params.MaxValidators = 1
	app.StakingKeeper.SetParams(ctx, params)

	h := newHelperx(t, ctx, app.StakingKeeper, app.BankKeeper)

	initTokens := scaledAmt(1000000000000)
	for _, delegator := range []string{d0, d1, d2} {
		require.NoError(t, simapp.FundAccount(app.BankKeeper, ctx, delegators[ix[delegator]], sdk.NewCoins(sdk.NewCoin(params.BondDenom, initTokens))))
	}

	h.createValidator(validators[0], PKs[0], 0, true)

	h.matchValidatorStatus(validators[ix[v0]], "unbonded")

	h.delegate(delegators[ix[d0]], validators[ix[v0]], 10000, true)

	for i := 0; i < 100; i++ {
		var dt = time.Duration(int64(5) * int64(time.Second))
		staking.EndBlocker(h.ctx, h.k)
		h.ctx = h.ctx.WithBlockTime(h.ctx.BlockHeader().Time.Add(dt))
	}

	h.matchValidatorStatus(validators[ix[v0]], "bonded")
}

func TestAdversarial(t *testing.T) {
	Adversarial(t)
}
