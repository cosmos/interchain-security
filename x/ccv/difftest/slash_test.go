package difftest_test

import (
	"fmt"
	"math/big"
	"math/rand"
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

const (
	v0 = "v0"
	d0 = "d0"
	d1 = "d1"
	d2 = "d2"
)

var (
	PKs = simapp.CreateTestPubKeys(500)
)

func tokensFromPower(power int64) sdk.Int {
	return sdk.TokensFromConsensusPower(int64(power), sdk.DefaultPowerReduction)
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

func (h *helperx) createValidator(addr sdk.ValAddress, pk cryptotypes.PubKey, tokens int64) {
	coin := sdk.NewCoin(h.denom, sdk.NewInt(tokens))
	zeroCommission := stakingtypes.NewCommissionRates(sdk.ZeroDec(), sdk.ZeroDec(), sdk.ZeroDec())
	msg, err := stakingtypes.NewMsgCreateValidator(addr, pk, coin, stakingtypes.Description{}, zeroCommission, sdk.ZeroInt())
	require.NoError(h.t, err)
	h.h(h.ctx, msg)
}

func (h *helperx) delegate(delegator sdk.AccAddress, val sdk.ValAddress, tokens int64) {
	coin := sdk.NewCoin(h.denom, sdk.NewInt(tokens))
	msg := stakingtypes.NewMsgDelegate(delegator, val, coin)
	h.h(h.ctx, msg)
}

func (h *helperx) undelegate(delegator sdk.AccAddress, val sdk.ValAddress, tokens int64) {
	coin := sdk.NewCoin(h.denom, sdk.NewInt(tokens))
	msg := stakingtypes.NewMsgUndelegate(delegator, val, coin)
	h.h(h.ctx, msg)
}

func (h *helperx) beginRedelegate(delegator sdk.AccAddress, src sdk.ValAddress, dst sdk.ValAddress, tokens int64) {
	coin := sdk.NewCoin(h.denom, sdk.NewInt(tokens))
	msg := stakingtypes.NewMsgBeginRedelegate(delegator, src, dst, coin)
	h.h(h.ctx, msg)
}

func (h *helperx) slash(val sdk.ValAddress, height int64, power int64, factor sdk.Dec) {
	cons := sdk.ConsAddress(val)
	h.k.Slash(h.ctx, cons, height, power, factor, -1)
}

func (h *helperx) matchValidatorStatus(val sdk.ValAddress, expect stakingtypes.BondStatus) {
	validator, _ := h.k.GetValidator(h.ctx, val)
	require.Equalf(h.t, expect, validator.GetStatus(), "exp: %s ", expect.String())
}

func (h *helperx) balance(addr sdk.AccAddress) int64 {
	return h.bk.GetBalance(h.ctx, addr, h.denom).Amount.Int64()
}

func (h *helperx) blocks(numBlocks int, secondsPerBlock int) {
	for i := 0; i < numBlocks; i++ {
		var dt = time.Duration(int64(secondsPerBlock) * int64(time.Second))
		staking.EndBlocker(h.ctx, h.k)
		h.ctx = h.ctx.WithBlockTime(h.ctx.BlockHeader().Time.Add(dt))
	}
}

func Adversarial(t *testing.T) {
	sdk.DefaultPowerReduction = sdk.NewIntFromBigInt(new(big.Int).Exp(big.NewInt(10), big.NewInt(9), nil))
	// sdk.DefaultPowerReduction = sdk.NewInt(1)
	secondsPerBlock := 5

	ix := make(map[string]int)
	ix[v0] = 0
	ix[d0] = 1
	ix[d1] = 2
	ix[d2] = 3

	numAddresses := 4
	app, ctx, delAddrs, valAddrs := bootstrapHandlerGenesisTest(t, int64(0), numAddresses, sdk.TokensFromConsensusPower(int64(0), sdk.DefaultPowerReduction))
	validators, delegators := valAddrs[:1], delAddrs

	params := app.StakingKeeper.GetParams(ctx)
	params.UnbondingTime = time.Duration(((rand.Intn(10) + 1) * secondsPerBlock)) * time.Second
	params.MaxValidators = 1
	app.StakingKeeper.SetParams(ctx, params)

	h := newHelperx(t, ctx, app.StakingKeeper, app.BankKeeper)

	initPower := int64(100000)
	initTokens := tokensFromPower(initPower)
	for _, delegator := range []string{d0, d1, d2} {
		require.NoError(t, simapp.FundAccount(app.BankKeeper, ctx, delegators[ix[delegator]], sdk.NewCoins(sdk.NewCoin(params.BondDenom, initTokens))))
	}

	h.createValidator(validators[0], PKs[0], 0)

	h.matchValidatorStatus(validators[ix[v0]], types.Unbonded)

	h.delegate(delegators[ix[d0]], validators[ix[v0]], 10000)

	h.blocks(1, 5)

	h.matchValidatorStatus(validators[ix[v0]], types.Bonded)
	require.Equal(h.t, h.balance(delegators[ix[d0]]), int64(90000))
	require.Equal(h.t, h.balance(delegators[ix[d1]]), int64(100000))
	require.Equal(h.t, h.balance(delegators[ix[d2]]), int64(100000))

	randomDelegator := func(enableBoth bool) string {
		if rand.Float64() < 0.5 && enableBoth {
			return d1
		}
		return d2
	}

	/*
			The execution that causes weirdness
			Slash         val0 15 30000 0.250000000000000000
			Slash         val0 15 30000 0.500000000000000000
			Undelegate    val2 del1 20000stake
		      issued:     20000
			Undelegate    val0 del1 10000stake
		      issued:     10000
			Slash         val0 115 50000 0.500000000000000000
			Slash         val1 15 40000 0.500000000000000000
			Delegate      val0 del1 20000stake
			Undelegate    val0 del1 10000stake
	*/

	doneSlash := false
	for i := 0; i < 10; i++ {
		j := rand.Intn(100)
		if j < 40 {
			h.blocks(rand.Intn(20), secondsPerBlock)
		} else if j < 60 {
			delegator := randomDelegator(doneSlash)
			// tokens := rand.Int63n(initTokens.Int64() + 10)
			tokens := rand.Int63n(h.balance(delegators[ix[delegator]]))
			h.delegate(delegators[ix[delegator]], validators[ix[v0]], tokens)
		} else if j < 80 {
			delegator := randomDelegator(doneSlash)
			tokens := rand.Int63n(initTokens.Int64() + 10)
			h.undelegate(delegators[ix[delegator]], validators[ix[v0]], tokens)
		} else if !doneSlash {
			doneSlash = true
			// tokens := rand.Int63n(initTokens.Int64())
			// power := sdk.TokensToConsensusPower(sdk.NewInt(tokens), sdk.DefaultPowerReduction)
			// height := rand.Int63n(h.ctx.BlockHeight() + 1)
			// factor := sdk.MustNewDecFromStr("0." + strconv.Itoa(rand.Intn(1000)))
			// h.slash(validators[ix[v0]], height, power, sdk.NewDec(1))

			v, e := h.k.GetValidator(h.ctx, validators[ix[v0]])
			require.True(t, e)
			fl := v.Tokens.ToDec().MustFloat64() * (rand.Float64()*0.8 + 0.1)
			flint := int64(fl)
			// fmt.Println("pre slash tokens ", v.Tokens)
			v.Tokens = sdk.NewInt(flint)
			// fmt.Println("post slash tokens ", v.Tokens)
			h.k.SetValidator(h.ctx, v)
		}
		// fmt.Println(h.balance(delegators[ix[d1]]), initTokens.Int64())
		// fmt.Println(h.balance(delegators[ix[d2]]), initTokens.Int64())
		// v, e := h.k.GetValidator(h.ctx, validators[ix[v0]])
		// require.True(t, e)
		// fmt.Println("shares ", v.GetDelegatorShares())
		require.LessOrEqual(h.t, h.balance(delegators[ix[d1]]), initTokens.Int64())
		require.LessOrEqual(h.t, h.balance(delegators[ix[d2]]), initTokens.Int64())
		h.matchValidatorStatus(validators[ix[v0]], types.Bonded)
	}

}

func TestAdversarial(t *testing.T) {
	rand.Seed(time.Now().UnixNano())
	for i := 0; i < 1000000; i++ {
		t.Run(fmt.Sprintf("%d", i), func(t *testing.T) {
			Adversarial(t)
		})
	}
}
