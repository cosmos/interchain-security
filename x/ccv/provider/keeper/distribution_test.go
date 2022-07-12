package keeper_test

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	distrtypes "github.com/cosmos/cosmos-sdk/x/distribution/types"

	appProvider "github.com/cosmos/interchain-security/app/provider"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
)

func (suite *KeeperTestSuite) TestDistribute() {
	app := suite.providerChain.App.(*appProvider.App)
	keeper := app.ProviderKeeper
	ctx := suite.ctx

	addresses := make([][]byte, len(suite.providerChain.Vals.Validators))
	weights := make([]sdk.Int, len(suite.providerChain.Vals.Validators))
	totalWeight := sdk.NewInt(0)
	suite.Require().EqualValues(4, len(suite.providerChain.Vals.Validators))

	for i, val := range suite.providerChain.Vals.Validators {
		addresses[i] = val.PubKey.Address()
		weights[i] = sdk.NewInt(100)
		totalWeight = totalWeight.Add(weights[i])
	}
	addresses = append(append(addresses, []byte("0xff")), []byte("0xee"))
	weights = append(append(weights, sdk.NewInt(100)), sdk.NewInt(100))
	totalWeight = totalWeight.Add(sdk.NewInt(200))

	// addresses = 4 exist validators + 2 non-exist validator
	// total weights = 600
	ppw1 := ccv.ProviderPoolWeights{
		Addresses:   addresses,
		Weights:     weights,
		TotalWeight: totalWeight,
		Tokens:      sdk.NewCoins(sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(100))),
	}

	ppw2 := ccv.ProviderPoolWeights{
		Addresses:   addresses,
		Weights:     weights,
		TotalWeight: totalWeight,
		Tokens:      sdk.NewCoins(sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(500))),
	}
	keeper.AddPendingProviderPoolWeights(ctx, &ppw1)
	keeper.AddPendingProviderPoolWeights(ctx, &ppw2)

	pendingPPWs := keeper.GetPendingProviderPoolWeights(ctx)
	suite.Require().EqualValues(2, len(pendingPPWs.GetPoolWeights()))

	distrAccount := app.AccountKeeper.GetModuleAddress(distrtypes.ModuleName)
	distrBalanceStart := app.BankKeeper.GetBalance(ctx, distrAccount, sdk.DefaultBondDenom)

	keeper.Distribute(ctx)
	pendingPPWs = keeper.GetPendingProviderPoolWeights(ctx)
	suite.Require().EqualValues(2, len(pendingPPWs.GetPoolWeights()))
	distrBalance := app.BankKeeper.GetBalance(ctx, distrAccount, sdk.DefaultBondDenom)
	suite.Require().EqualValues(distrBalanceStart.Amount, distrBalance.Amount)

	err := app.BankKeeper.SendCoinsFromAccountToModule(ctx, suite.providerChain.SenderAccounts[0].SenderAccount.GetAddress(), types.DistributionAccount, sdk.NewCoins(sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(100))))
	suite.Require().NoError(err)
	keeper.Distribute(ctx)
	pendingPPWs = keeper.GetPendingProviderPoolWeights(ctx)
	suite.Require().EqualValues(1, len(pendingPPWs.GetPoolWeights()))
	suite.Require().EqualValues(500, pendingPPWs.GetPoolWeights()[0].Tokens[0].Amount.Int64())
	distrBalance = app.BankKeeper.GetBalance(ctx, distrAccount, sdk.DefaultBondDenom)
	suite.Require().EqualValues(distrBalanceStart.Amount.Add(sdk.NewInt(100)), distrBalance.Amount)
	// excess = 100 - 16 * 4 = 36
	excessPool := keeper.GetDistributionExcessPool(ctx)
	suite.Require().EqualValues(36, excessPool.Excess[0].Amount.Int64())

	err = app.BankKeeper.SendCoinsFromAccountToModule(ctx, suite.providerChain.SenderAccounts[0].SenderAccount.GetAddress(), types.DistributionAccount, sdk.NewCoins(sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(500))))
	suite.Require().NoError(err)
	keeper.Distribute(ctx)
	pendingPPWs = keeper.GetPendingProviderPoolWeights(ctx)
	suite.Require().EqualValues(0, len(pendingPPWs.GetPoolWeights()))
	distrBalance = app.BankKeeper.GetBalance(ctx, distrAccount, sdk.DefaultBondDenom)
	suite.Require().EqualValues(distrBalanceStart.Amount.Add(sdk.NewInt(600)), distrBalance.Amount)
	// excess = excess + (500 - 83 * 4) = 204
	excessPool = keeper.GetDistributionExcessPool(ctx)
	suite.Require().EqualValues(204, excessPool.Excess[0].Amount.Int64())
}
