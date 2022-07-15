// package difftest_test

// import (
// 	"bytes"
// 	"testing"
// 	"time"

// 	"github.com/cosmos/cosmos-sdk/codec"
// 	cryptotypes "github.com/cosmos/cosmos-sdk/crypto/types"
// 	"github.com/cosmos/cosmos-sdk/simapp"
// 	sdk "github.com/cosmos/cosmos-sdk/types"
// 	"github.com/cosmos/cosmos-sdk/x/staking"
// 	"github.com/cosmos/cosmos-sdk/x/staking/keeper"
// 	"github.com/cosmos/cosmos-sdk/x/staking/types"
// 	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
// 	"github.com/stretchr/testify/require"
// 	tmproto "github.com/tendermint/tendermint/proto/tendermint/types"
// )

// var (
// 	priv1 = secp256k1.GenPrivKey()
// 	addr1 = sdk.AccAddress(priv1.PubKey().Address())
// 	priv2 = secp256k1.GenPrivKey()
// 	addr2 = sdk.AccAddress(priv2.PubKey().Address())

// 	valKey  = ed25519.GenPrivKey()
// 	valAddr = sdk.AccAddress(valKey.PubKey().Address())

// 	commissionRates = types.NewCommissionRates(sdk.ZeroDec(), sdk.ZeroDec(), sdk.ZeroDec())

// PKs = simapp.CreateTestPubKeys(500)
// )

// func getBaseSimappWithCustomKeeper() (*codec.LegacyAmino, *simapp.SimApp, sdk.Context) {
// 	app := simapp.Setup(false)
// 	ctx := app.BaseApp.NewContext(false, tmproto.Header{})

// 	appCodec := app.AppCodec()

// 	app.StakingKeeper = keeper.NewKeeper(
// 		appCodec,
// 		app.GetKey(types.StoreKey),
// 		app.AccountKeeper,
// 		app.BankKeeper,
// 		app.GetSubspace(types.ModuleName),
// 	)
// 	app.StakingKeeper.SetParams(ctx, types.DefaultParams())

// 	return codec.NewLegacyAmino(), app, ctx
// }

// func generateAddresses(app *simapp.SimApp, ctx sdk.Context, numAddrs int, accAmount sdk.Int) ([]sdk.AccAddress, []sdk.ValAddress) {
// 	addrDels := simapp.AddTestAddrsIncremental(app, ctx, numAddrs, accAmount)
// 	addrVals := simapp.ConvertAddrsToValAddrs(addrDels)

// 	return addrDels, addrVals
// }

// func bootstrapHandlerGenesisTest(t *testing.T, power int64, numAddrs int, accAmount sdk.Int) (*simapp.SimApp, sdk.Context, []sdk.AccAddress, []sdk.ValAddress) {
// 	_, app, ctx := getBaseSimappWithCustomKeeper()

// 	addrDels, addrVals := generateAddresses(app, ctx, numAddrs, accAmount)

// 	amt := app.StakingKeeper.TokensFromConsensusPower(ctx, power)
// 	totalSupply := sdk.NewCoins(sdk.NewCoin(app.StakingKeeper.BondDenom(ctx), amt.MulRaw(int64(len(addrDels)))))

// 	notBondedPool := app.StakingKeeper.GetNotBondedPool(ctx)

// 	// set non bonded pool balance
// 	app.AccountKeeper.SetModuleAccount(ctx, notBondedPool)
// 	require.NoError(t, simapp.FundModuleAccount(app.BankKeeper, ctx, notBondedPool.GetName(), totalSupply))
// 	return app, ctx, addrDels, addrVals
// }

// func scaledAmt(modelAmt int) sdk.Int {
// 	return sdk.TokensFromConsensusPower(int64(modelAmt), sdk.DefaultPowerReduction)
// }

// type helper struct {
// 	t          *testing.T
// 	h          sdk.Handler
// 	k          keeper.Keeper
// 	bk         types.BankKeeper
// 	ctx        sdk.Context
// 	commission stakingtypes.CommissionRates
// 	denom      string
// }

// // constructs a commission rates with all zeros.
// func zeroCommission() stakingtypes.CommissionRates {
// 	return stakingtypes.NewCommissionRates(sdk.ZeroDec(), sdk.ZeroDec(), sdk.ZeroDec())
// }

// // creates staking Handler wrapper for tests
// func newHelper(t *testing.T, ctx sdk.Context, k keeper.Keeper, bk types.BankKeeper) *helper {
// 	return &helper{t, staking.NewHandler(k), k, bk, ctx, zeroCommission(), sdk.DefaultBondDenom}
// }

// // calls handler to create a new staking validator
// func (h *helper) createValidator(addr sdk.ValAddress, pk cryptotypes.PubKey, stakeAmt int, ok bool) {
// 	coin := sdk.NewCoin(h.denom, scaledAmt(stakeAmt))
// 	msg, err := stakingtypes.NewMsgCreateValidator(addr, pk, coin, stakingtypes.Description{}, h.commission, sdk.OneInt())
// 	require.NoError(h.t, err)
// 	h.handle(msg, ok)
// }

// // calls handler to delegate stake for a validator
// func (h *helper) delegate(delegator sdk.AccAddress, val sdk.ValAddress, amt int, ok bool) {
// 	coin := sdk.NewCoin(h.denom, scaledAmt(amt))
// 	msg := stakingtypes.NewMsgDelegate(delegator, val, coin)
// 	h.handle(msg, ok)
// }

// // calls handler to unbound some stake from a validator.
// func (h *helper) undelegate(delegator sdk.AccAddress, val sdk.ValAddress, amt int, ok bool) *sdk.Result {
// 	coin := sdk.NewCoin(h.denom, scaledAmt(amt))
// 	msg := stakingtypes.NewMsgUndelegate(delegator, val, coin)
// 	return h.handle(msg, ok)
// }

// // calls handler to redelegate funds from src to dst
// func (h *helper) beginRedelegate(delegator sdk.AccAddress, src sdk.ValAddress, dst sdk.ValAddress, amt int, ok bool) *sdk.Result {
// 	coin := sdk.NewCoin(h.denom, scaledAmt(amt))
// 	msg := stakingtypes.NewMsgBeginRedelegate(delegator, src, dst, coin)
// 	return h.handle(msg, ok)
// }

// func (h *helper) matchValidatorStatus(val sdk.ValAddress, status string) {
// 	validator, _ := h.k.GetValidator(h.ctx, val)
// 	actual := validator.GetStatus()
// 	if status == "bonded" {
// 		require.Equal(h.t, types.Bonded, actual)
// 	}
// 	if status == "unbonding" {
// 		require.Equal(h.t, types.Unbonding, actual)
// 	}
// 	if status == "unbonded" {
// 		require.Equal(h.t, types.Unbonded, actual)
// 	}
// }

// func (h *helper) matchBalance(addr sdk.AccAddress, amt int) {
// 	bal := h.bk.GetBalance(h.ctx, addr, h.denom)
// 	exp := sdk.NewCoin(h.denom, scaledAmt(amt))
// 	require.Equal(h.t, exp, bal)
// }

// func (h *helper) matchTokens(addr sdk.ValAddress, amt int) {
// 	validator, _ := h.k.GetValidator(h.ctx, addr)
// 	tok := validator.Tokens
// 	exp := scaledAmt(amt)
// 	require.Equal(h.t, exp, tok)
// }

// func (h *helper) matchDelegation(delegator sdk.AccAddress, val sdk.ValAddress, amt int) {
// 	del, found := h.k.GetDelegation(h.ctx, delegator, val)
// 	if 0 < amt {
// 		require.True(h.t, found)
// 		shares := del.Shares
// 		scaled := scaledAmt(amt)
// 		exp := sdk.NewDec(scaled.Int64())
// 		require.Equal(h.t, exp, shares)
// 	}
// 	if 0 == amt {
// 		require.False(h.t, found)
// 	}
// }

// func (h *helper) ensureValidatorLexicographicOrderingMatchesModel(v0 sdk.ValAddress, v1 sdk.ValAddress) {
// 	/*
// 		Ties in validator power are broken based on comparing PowerIndexKey. The model tie-break needs
// 		to match the code tie-break at all times. This function ensures the tie break function in the model
// 		is correct.
// 	*/
// 	xv, _ := h.k.GetValidator(h.ctx, v0)
// 	yv, _ := h.k.GetValidator(h.ctx, v1)
// 	xk := types.GetValidatorsByPowerIndexKey(xv, sdk.DefaultPowerReduction)
// 	yk := types.GetValidatorsByPowerIndexKey(yv, sdk.DefaultPowerReduction)
// 	// The result will be 0 if a==b, -1 if a < b, and +1 if a > b.
// 	res := bytes.Compare(xk, yk)
// 	// Confirm that validator precedence is the same in code as in model
// 	require.Equal(h.t, 1, res)
// }

// // handle calls staking handler on a given message
// func (h *helper) handle(msg sdk.Msg, ok bool) *sdk.Result {
// 	res, err := h.h(h.ctx, msg)
// 	if ok {
// 		require.NoError(h.t, err)
// 		require.NotNil(h.t, res)
// 	} else {
// 		require.Error(h.t, err)
// 		require.Nil(h.t, res)
// 	}
// 	return res
// }

// func ExecuteTrace(t *testing.T) {
// 	ix := make(map[string]int)
// 	ix["v0"] = 0
// 	ix["v1"] = 1
// 	ix["d0"] = 4

// 	initPower := int64(0)
// 	numAddresses := 6
// 	app, ctx, delAddrs, valAddrs := bootstrapHandlerGenesisTest(t, initPower, numAddresses, sdk.TokensFromConsensusPower(initPower, sdk.DefaultPowerReduction))
// 	validators, delegators := valAddrs[:3], delAddrs

// 	params := app.StakingKeeper.GetParams(ctx)
// 	params.UnbondingTime = 2 * time.Second
// 	params.MaxValidators = 1
// 	app.StakingKeeper.SetParams(ctx, params)

// 	h := newHelper(t, ctx, app.StakingKeeper, app.BankKeeper)

// 	var states = trace.States
// 	var init = states[0]
// 	states = states[1:]

// 	require.NoError(t, simapp.FundAccount(app.BankKeeper, ctx, delegators[ix["v0"]], sdk.NewCoins(sdk.NewCoin(params.BondDenom, scaledAmt(init.Tokens.V0)))))
// 	require.NoError(t, simapp.FundAccount(app.BankKeeper, ctx, delegators[ix["v1"]], sdk.NewCoins(sdk.NewCoin(params.BondDenom, scaledAmt(init.Tokens.V1)))))
// 	require.NoError(t, simapp.FundAccount(app.BankKeeper, ctx, delegators[ix["d0"]], sdk.NewCoins(sdk.NewCoin(params.BondDenom, scaledAmt(init.Tokens.D0)))))

// 	h.createValidator(validators[0], PKs[0], 1, true)
// 	h.createValidator(validators[1], PKs[1], 1, true)

// 	h.ensureValidatorLexicographicOrderingMatchesModel(validators[ix["v0"]], validators[ix["v1"]])

// 	h.matchValidatorStatus(validators[ix["v0"]], init.Status.V0)
// 	h.matchValidatorStatus(validators[ix["v1"]], init.Status.V1)

// 	for _, state := range states {
// 		var succeed = state.Outcome == "succeed"
// 		switch state.Action.Nature {
// 		case "endBlock":
// 			// Does this make sense?
// 			var dt = time.Duration(int64(state.Action.TimeDelta) * int64(time.Second))
// 			staking.EndBlocker(h.ctx, h.k)
// 			h.ctx = h.ctx.WithBlockTime(h.ctx.BlockHeader().Time.Add(dt))
// 		case "delegate":
// 			var del = delegators[ix[state.Action.Delegator]]
// 			var val = validators[ix[state.Action.Validator]]
// 			h.delegate(del, val, state.Action.Amount, succeed)
// 		case "undelegate":
// 			var del = delegators[ix[state.Action.Delegator]]
// 			var val = validators[ix[state.Action.Validator]]
// 			h.undelegate(del, val, state.Action.Amount, succeed)
// 		case "beginRedelegate":
// 			var del = delegators[ix[state.Action.Delegator]]
// 			var src = validators[ix[state.Action.ValidatorSrc]]
// 			var dst = validators[ix[state.Action.ValidatorDst]]
// 			h.beginRedelegate(del, src, dst, state.Action.Amount, succeed)
// 		}
// 		h.matchValidatorStatus(validators[ix["v0"]], state.Status.V0)
// 		h.matchValidatorStatus(validators[ix["v1"]], state.Status.V1)
// 		h.matchBalance(delegators[ix["d0"]], state.Tokens.D0)
// 		h.matchTokens(validators[ix["v0"]], state.Tokens.V0)
// 		h.matchTokens(validators[ix["v1"]], state.Tokens.V1)
// 		h.matchDelegation(delegators[ix["v0"]], validators[ix["v0"]], state.Delegation.delegation("v0", "v0"))
// 		h.matchDelegation(delegators[ix["v1"]], validators[ix["v1"]], state.Delegation.delegation("v1", "v1"))
// 		h.matchDelegation(delegators[ix["d0"]], validators[ix["v0"]], state.Delegation.delegation("d0", "v0"))
// 		h.matchDelegation(delegators[ix["d0"]], validators[ix["v1"]], state.Delegation.delegation("d0", "v1"))
// 	}
// }
