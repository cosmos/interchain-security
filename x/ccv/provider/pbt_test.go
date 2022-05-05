package provider_test

import (
	"testing"

	sdk "github.com/cosmos/cosmos-sdk/types"

	transfertypes "github.com/cosmos/ibc-go/v3/modules/apps/transfer/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	commitmenttypes "github.com/cosmos/ibc-go/v3/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"

	appConsumer "github.com/cosmos/interchain-security/app_consumer"
	appProvider "github.com/cosmos/interchain-security/app_provider"
	"github.com/cosmos/interchain-security/testutil/simapp"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	"github.com/cosmos/interchain-security/x/ccv/types"

	tmtypes "github.com/tendermint/tendermint/types"

	"bytes"
	"testing"
	"time"

	"github.com/stretchr/testify/suite"

	cryptotypes "github.com/cosmos/cosmos-sdk/crypto/types"
	"github.com/cosmos/cosmos-sdk/simapp"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/x/staking"
	"github.com/cosmos/cosmos-sdk/x/staking/keeper"
	"github.com/cosmos/cosmos-sdk/x/staking/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	"github.com/stretchr/testify/require"
)

type PBTTestSuite struct {
	suite.Suite

	coordinator *ibctesting.Coordinator

	providerChain *ibctesting.TestChain
	consumerChain *ibctesting.TestChain

	providerClient    *ibctmtypes.ClientState
	providerConsState *ibctmtypes.ConsensusState
	consumerClient    *ibctmtypes.ClientState
	consumerConsState *ibctmtypes.ConsensusState

	path *ibctesting.Path

	ctx sdk.Context
}

func (suite *PBTTestSuite) SetupTest() {

	suite.coordinator, suite.providerChain, suite.consumerChain = simapp.NewProviderConsumerCoordinator(suite.T())

	suite.DisableConsumerDistribution()

	tmConfig := ibctesting.NewTendermintConfig()

	// commit a block on provider chain before creating client
	suite.coordinator.CommitBlock(suite.providerChain)

	// create client and consensus state of provider chain to initialize consumer chain genesis.
	height := suite.providerChain.LastHeader.GetHeight().(clienttypes.Height)
	UpgradePath := []string{"upgrade", "upgradedIBCState"}

	suite.providerClient = ibctmtypes.NewClientState(
		suite.providerChain.ChainID, tmConfig.TrustLevel, tmConfig.TrustingPeriod, tmConfig.UnbondingPeriod, tmConfig.MaxClockDrift,
		height, commitmenttypes.GetSDKSpecs(), UpgradePath, tmConfig.AllowUpdateAfterExpiry, tmConfig.AllowUpdateAfterMisbehaviour,
	)
	suite.providerConsState = suite.providerChain.LastHeader.ConsensusState()

	valUpdates := tmtypes.TM2PB.ValidatorUpdates(suite.providerChain.Vals)

	params := consumertypes.NewParams(
		true,
		1000, // about 2 hr at 7.6 seconds per blocks
		"",
		"",
		"0.5", // 50%
	)
	consumerGenesis := consumertypes.NewInitialGenesisState(suite.providerClient, suite.providerConsState, valUpdates, params)
	suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.InitGenesis(suite.consumerChain.GetContext(), consumerGenesis)

	suite.ctx = suite.providerChain.GetContext()

	suite.path = ibctesting.NewPath(suite.consumerChain, suite.providerChain)
	suite.path.EndpointA.ChannelConfig.PortID = consumertypes.PortID
	suite.path.EndpointB.ChannelConfig.PortID = providertypes.PortID
	suite.path.EndpointA.ChannelConfig.Version = types.Version
	suite.path.EndpointB.ChannelConfig.Version = types.Version
	suite.path.EndpointA.ChannelConfig.Order = channeltypes.ORDERED
	suite.path.EndpointB.ChannelConfig.Order = channeltypes.ORDERED
	providerClient, ok := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetProviderClient(suite.consumerChain.GetContext())
	if !ok {
		panic("must already have provider client on consumer chain")
	}
	// set consumer endpoint's clientID
	suite.path.EndpointA.ClientID = providerClient

	// TODO: No idea why or how this works, but it seems that it needs to be done.
	suite.path.EndpointB.Chain.SenderAccount.SetAccountNumber(6)
	suite.path.EndpointA.Chain.SenderAccount.SetAccountNumber(6)

	// create consumer client on provider chain and set as consumer client for consumer chainID in provider keeper.
	suite.path.EndpointB.CreateClient()
	suite.providerChain.App.(*appProvider.App).ProviderKeeper.SetConsumerClient(suite.providerChain.GetContext(), suite.consumerChain.ChainID, suite.path.EndpointB.ClientID)

	suite.path = ibctesting.NewPath(suite.consumerChain, suite.providerChain)
	suite.path EndpointA.ChannelConfig.PortID = transfertypes.PortID
	suite.path EndpointB.ChannelConfig.PortID = transfertypes.PortID
	suite.path EndpointA.ChannelConfig.Version = transfertypes.Version
	suite.path EndpointB.ChannelConfig.Version = transfertypes.Version
}

func (suite *PBTTestSuite) SetupCCVChannel() {
	suite.coordinator.CreateConnections(suite.path)

	// CCV channel handshake will automatically initiate transfer channel handshake on ACK
	// so transfer channel will be on stage INIT when CreateChannels for ccv path returns.
	suite.coordinator.CreateChannels(suite.path)

	// transfer path will use the same connection as ccv path

	suite.path EndpointA.ClientID = suite.path.EndpointA.ClientID
	suite.path EndpointA.ConnectionID = suite.path.EndpointA.ConnectionID
	suite.path EndpointB.ClientID = suite.path.EndpointB.ClientID
	suite.path EndpointB.ConnectionID = suite.path.EndpointB.ConnectionID

	// INIT step for transfer path has already been called during CCV channel setup
	suite.path EndpointA.ChannelID = suite.consumerChain.App.(*appConsumer.App).
		ConsumerKeeper.GetDistributionTransmissionChannel(suite.consumerChain.GetContext())

	// Complete TRY, ACK, CONFIRM for transfer path
	err := suite.path EndpointB.ChanOpenTry()
	suite.Require().NoError(err)

	err = suite.path EndpointA.ChanOpenAck()
	suite.Require().NoError(err)

	err = suite.path EndpointB.ChanOpenConfirm()
	suite.Require().NoError(err)

	// ensure counterparty is up to date
	suite.path EndpointA.UpdateClient()
}

func TestProviderTestSuite(t *testing.T) {
	suite.Run(t, new(PBTTestSuite))
}

func scaledAmt(modelAmt int) sdk.Int {
	return sdk.TokensFromConsensusPower(int64(modelAmt), sdk.DefaultPowerReduction)
}

type helper struct {
	t          *testing.T
	h          sdk.Handler
	k          keeper.Keeper
	bk         types.BankKeeper
	ctx        sdk.Context
	commission stakingtypes.CommissionRates
	denom      string
}

// constructs a commission rates with all zeros.
func zeroCommission() stakingtypes.CommissionRates {
	return stakingtypes.NewCommissionRates(sdk.ZeroDec(), sdk.ZeroDec(), sdk.ZeroDec())
}

// creates staking Handler wrapper for tests
func newHelper(t *testing.T, ctx sdk.Context, k keeper.Keeper, bk types.BankKeeper) *helper {
	return &helper{t, staking.NewHandler(k), k, bk, ctx, zeroCommission(), sdk.DefaultBondDenom}
}

// calls handler to create a new staking validator
func (h *helper) createValidator(addr sdk.ValAddress, pk cryptotypes.PubKey, stakeAmt int, ok bool) {
	coin := sdk.NewCoin(h.denom, scaledAmt(stakeAmt))
	msg, err := stakingtypes.NewMsgCreateValidator(addr, pk, coin, stakingtypes.Description{}, h.commission, sdk.OneInt())
	require.NoError(h.t, err)
	h.handle(msg, ok)
}

// calls handler to delegate stake for a validator
func (h *helper) delegate(delegator sdk.AccAddress, val sdk.ValAddress, amt int, ok bool) {
	coin := sdk.NewCoin(h.denom, scaledAmt(amt))
	msg := stakingtypes.NewMsgDelegate(delegator, val, coin)
	h.handle(msg, ok)
}

// calls handler to unbound some stake from a validator.
func (h *helper) undelegate(delegator sdk.AccAddress, val sdk.ValAddress, amt int, ok bool) *sdk.Result {
	coin := sdk.NewCoin(h.denom, scaledAmt(amt))
	msg := stakingtypes.NewMsgUndelegate(delegator, val, coin)
	return h.handle(msg, ok)
}

// calls handler to redelegate funds from src to dst
func (h *helper) beginRedelegate(delegator sdk.AccAddress, src sdk.ValAddress, dst sdk.ValAddress, amt int, ok bool) *sdk.Result {
	coin := sdk.NewCoin(h.denom, scaledAmt(amt))
	msg := stakingtypes.NewMsgBeginRedelegate(delegator, src, dst, coin)
	return h.handle(msg, ok)
}

func (h *helper) matchValidatorStatus(val sdk.ValAddress, status string) {
	validator, _ := h.k.GetValidator(h.ctx, val)
	actual := validator.GetStatus()
	if status == "bonded" {
		require.Equal(h.t, types.Bonded, actual)
	}
	if status == "unbonding" {
		require.Equal(h.t, types.Unbonding, actual)
	}
	if status == "unbonded" {
		require.Equal(h.t, types.Unbonded, actual)
	}
}

func (h *helper) matchBalance(addr sdk.AccAddress, amt int) {
	bal := h.bk.GetBalance(h.ctx, addr, h.denom)
	exp := sdk.NewCoin(h.denom, scaledAmt(amt))
	require.Equal(h.t, exp, bal)
}

func (h *helper) matchTokens(addr sdk.ValAddress, amt int) {
	validator, _ := h.k.GetValidator(h.ctx, addr)
	tok := validator.Tokens
	exp := scaledAmt(amt)
	require.Equal(h.t, exp, tok)
}

func (h *helper) matchDelegation(delegator sdk.AccAddress, val sdk.ValAddress, amt int) {
	del, found := h.k.GetDelegation(h.ctx, delegator, val)
	if 0 < amt {
		require.True(h.t, found)
		shares := del.Shares
		scaled := scaledAmt(amt)
		exp := sdk.NewDec(scaled.Int64())
		require.Equal(h.t, exp, shares)
	}
	if 0 == amt {
		require.False(h.t, found)
	}
}

func (h *helper) ensureValidatorLexicographicOrderingMatchesModel(v0 sdk.ValAddress, v1 sdk.ValAddress) {
	/*
		Ties in validator power are broken based on comparing PowerIndexKey. The model tie-break needs
		to match the code tie-break at all times. This function ensures the tie break function in the model
		is correct.
	*/
	xv, _ := h.k.GetValidator(h.ctx, v0)
	yv, _ := h.k.GetValidator(h.ctx, v1)
	xk := types.GetValidatorsByPowerIndexKey(xv, sdk.DefaultPowerReduction)
	yk := types.GetValidatorsByPowerIndexKey(yv, sdk.DefaultPowerReduction)
	// The result will be 0 if a==b, -1 if a < b, and +1 if a > b.
	res := bytes.Compare(xk, yk)
	// Confirm that validator precedence is the same in code as in model
	require.Equal(h.t, 1, res)
}

// handle calls staking handler on a given message
func (h *helper) handle(msg sdk.Msg, ok bool) *sdk.Result {
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

func ExecuteTrace(t *testing.T, trace trace) {
	ix := make(map[string]int)
	ix["v0"] = 0
	ix["v1"] = 1
	ix["d0"] = 4

	initPower := int64(0)
	numAddresses := 6
	app, ctx, delAddrs, valAddrs := bootstrapHandlerGenesisTest(t, initPower, numAddresses, sdk.TokensFromConsensusPower(initPower, sdk.DefaultPowerReduction))
	validators, delegators := valAddrs[:3], delAddrs

	params := app.StakingKeeper.GetParams(ctx)
	params.UnbondingTime = 2 * time.Second
	params.MaxValidators = 1
	app.StakingKeeper.SetParams(ctx, params)

	h := newHelper(t, ctx, app.StakingKeeper, app.BankKeeper)

	var states = trace.States
	var init = states[0]
	states = states[1:]

	require.NoError(t, simapp.FundAccount(app.BankKeeper, ctx, delegators[ix["v0"]], sdk.NewCoins(sdk.NewCoin(params.BondDenom, scaledAmt(init.Tokens.V0)))))
	require.NoError(t, simapp.FundAccount(app.BankKeeper, ctx, delegators[ix["v1"]], sdk.NewCoins(sdk.NewCoin(params.BondDenom, scaledAmt(init.Tokens.V1)))))
	require.NoError(t, simapp.FundAccount(app.BankKeeper, ctx, delegators[ix["d0"]], sdk.NewCoins(sdk.NewCoin(params.BondDenom, scaledAmt(init.Tokens.D0)))))

	h.createValidator(validators[0], PKs[0], 1, true)
	h.createValidator(validators[1], PKs[1], 1, true)

	h.ensureValidatorLexicographicOrderingMatchesModel(validators[ix["v0"]], validators[ix["v1"]])

	h.matchValidatorStatus(validators[ix["v0"]], init.Status.V0)
	h.matchValidatorStatus(validators[ix["v1"]], init.Status.V1)

	for _, state := range states {
		var succeed = state.Outcome == "succeed"
		switch state.Action.Nature {
		case "endBlock":
			// Does this make sense?
			var dt = time.Duration(int64(state.Action.TimeDelta) * int64(time.Second))
			staking.EndBlocker(h.ctx, h.k)
			h.ctx = h.ctx.WithBlockTime(h.ctx.BlockHeader().Time.Add(dt))
		case "delegate":
			var del = delegators[ix[state.Action.Delegator]]
			var val = validators[ix[state.Action.Validator]]
			h.delegate(del, val, state.Action.Amount, succeed)
		case "undelegate":
			var del = delegators[ix[state.Action.Delegator]]
			var val = validators[ix[state.Action.Validator]]
			h.undelegate(del, val, state.Action.Amount, succeed)
		case "beginRedelegate":
			var del = delegators[ix[state.Action.Delegator]]
			var src = validators[ix[state.Action.ValidatorSrc]]
			var dst = validators[ix[state.Action.ValidatorDst]]
			h.beginRedelegate(del, src, dst, state.Action.Amount, succeed)
		}
		h.matchValidatorStatus(validators[ix["v0"]], state.Status.V0)
		h.matchValidatorStatus(validators[ix["v1"]], state.Status.V1)
		h.matchBalance(delegators[ix["d0"]], state.Tokens.D0)
		h.matchTokens(validators[ix["v0"]], state.Tokens.V0)
		h.matchTokens(validators[ix["v1"]], state.Tokens.V1)
		h.matchDelegation(delegators[ix["v0"]], validators[ix["v0"]], state.Delegation.delegation("v0", "v0"))
		h.matchDelegation(delegators[ix["v1"]], validators[ix["v1"]], state.Delegation.delegation("v1", "v1"))
		h.matchDelegation(delegators[ix["d0"]], validators[ix["v0"]], state.Delegation.delegation("d0", "v0"))
		h.matchDelegation(delegators[ix["d0"]], validators[ix["v1"]], state.Delegation.delegation("d0", "v1"))
	}
}
