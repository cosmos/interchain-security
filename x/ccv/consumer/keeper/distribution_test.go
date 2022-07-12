package keeper_test

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	"github.com/cosmos/interchain-security/x/ccv/consumer/types"
	abci "github.com/tendermint/tendermint/abci/types"
	types1 "github.com/tendermint/tendermint/proto/tendermint/types"
)

func (suite *KeeperTestSuite) TestDistribute() {
	app := suite.consumerChain.App.(*appConsumer.App)
	keeper := app.ConsumerKeeper

	proposer := suite.consumerChain.Vals.Validators[0]
	ctx := suite.consumerChain.GetContext()
	voteInfos := make([]abci.VoteInfo, len(suite.consumerChain.Vals.Validators))
	var totalVotingPower int64
	for i, val := range suite.consumerChain.Vals.Validators {
		signedLastBlock := true
		if i == len(suite.consumerChain.Vals.Validators)-1 {
			signedLastBlock = false
		}
		vi := abci.VoteInfo{
			Validator: abci.Validator{
				Address: val.PubKey.Address(),
				Power:   val.VotingPower,
			},
			SignedLastBlock: signedLastBlock,
		}
		voteInfos[i] = vi
		totalVotingPower += val.VotingPower
	}

	keeper.Distribute(ctx, abci.RequestBeginBlock{
		Header: types1.Header{
			ProposerAddress: proposer.PubKey.Address().Bytes(),
		},
	})
	previousProposer := keeper.GetPreviousProposerConsAddr(ctx)
	suite.Require().EqualValues(proposer.PubKey.Address().Bytes(), previousProposer)

	// next block
	ctx.WithBlockHeight(ctx.BlockHeader().Height + 1)

	err := app.BankKeeper.SendCoinsFromAccountToModule(ctx, suite.consumerChain.SenderAccounts[0].SenderAccount.GetAddress(), "fee_collector", sdk.NewCoins(sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(100))))
	suite.Require().NoError(err)

	lastCommitInfo := abci.LastCommitInfo{
		Votes: voteInfos,
	}
	req := abci.RequestBeginBlock{
		Header: types1.Header{
			ProposerAddress: proposer.PubKey.Address().Bytes(),
		},
		LastCommitInfo: lastCommitInfo,
	}
	keeper.Distribute(ctx, req)

	redistributeAcc := app.AccountKeeper.GetModuleAddress(types.ConsumerRedistributeName)
	balance := app.BankKeeper.GetBalance(ctx, redistributeAcc, sdk.DefaultBondDenom)
	suite.Require().EqualValues(balance.Amount.Int64(), 75)

	prsAcc := app.AccountKeeper.GetModuleAddress(types.ProviderRewardStagingName)
	prsBalance := app.BankKeeper.GetBalance(ctx, prsAcc, sdk.DefaultBondDenom)
	suite.Require().EqualValues(prsBalance.Amount.Int64(), 25)

	proposerMultiplier := sdk.NewDecWithPrec(4, 2)
	var expectedTotalPower int64
	for i, val := range suite.consumerChain.Vals.Validators {
		expectedVotingPower := val.VotingPower
		if i == 0 {
			expectedVotingPower = expectedVotingPower + sdk.NewDec(totalVotingPower).MulTruncate(proposerMultiplier).RoundInt64()
		}
		vhp, found := keeper.GetProviderValidatorHoldingPool(ctx, val.PubKey.Address().Bytes())
		suite.Require().True(found)
		suite.Require().EqualValues(vhp.Weight.Int64(), expectedVotingPower)
		expectedTotalPower += expectedVotingPower
	}

	//
	err = keeper.DistributeToProviderValidatorSetV2(ctx)
	suite.Require().NoError(err)
	var count int
	keeper.IterateValidatorHoldingPools(ctx, func(valAddr []byte, weight sdk.Int) bool {
		count++
		return false
	})
	suite.Require().EqualValues(len(suite.consumerChain.Vals.Validators), count)

	ctx = ctx.WithBlockHeight(1000)
	err = keeper.DistributeToProviderValidatorSetV2(ctx)
	suite.Require().NoError(err)

	count = 0 // reset count
	keeper.IterateValidatorHoldingPools(ctx, func(valAddr []byte, weight sdk.Int) bool {
		count++
		return false
	})
	suite.Require().EqualValues(0, count)

	prsBalance = app.BankKeeper.GetBalance(ctx, prsAcc, sdk.DefaultBondDenom)
	suite.Require().EqualValues(0, prsBalance.Amount.Int64())

	ctstpAcc := app.AccountKeeper.GetModuleAddress(types.ConsumerToSendToProviderName)
	ctstpBalance := app.BankKeeper.GetBalance(ctx, ctstpAcc, sdk.DefaultBondDenom)
	suite.Require().EqualValues(25, ctstpBalance.Amount.Int64())

	ppws := keeper.GetPendingProviderPoolWeights(ctx)
	suite.Require().EqualValues(1, len(ppws))

	ppw := ppws[0]
	suite.Require().EqualValues(4, len(ppw.Addresses))
	suite.Require().EqualValues(len(ppw.Addresses), len(ppw.Weights))
	suite.Require().EqualValues(expectedTotalPower, ppw.TotalWeight.Int64())
	suite.Require().EqualValues(25, ppw.Tokens.AmountOf(sdk.DefaultBondDenom).Int64())

	keeper.ClearPendingProviderPoolWeights(ctx)
	ppws = keeper.GetPendingProviderPoolWeights(ctx)
	suite.Require().Nil(ppws)
}
