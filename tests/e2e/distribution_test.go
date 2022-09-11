package e2e_test

import (
	"strings"

	sdk "github.com/cosmos/cosmos-sdk/types"
	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"
	transfertypes "github.com/cosmos/ibc-go/v3/modules/apps/transfer/types"
	app "github.com/cosmos/interchain-security/app/consumer"
	providerApp "github.com/cosmos/interchain-security/app/provider"
	consumerkeeper "github.com/cosmos/interchain-security/x/ccv/consumer/keeper"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
)

//This test is valid for minimal viable consumer chain
func (s *ProviderTestSuite) TestRewardsDistribution() {

	//set up channel and delegate some tokens in order for validator set update to be sent to the consumer chain
	s.SetupCCVChannel()
	bondAmt := sdk.NewInt(10000000)
	delAddr := s.providerChain.SenderAccount.GetAddress()
	delegate(s, delAddr, bondAmt)
	s.providerChain.NextBlock()

	// relay VSC packets from provider to consumer
	relayAllCommittedPackets(s, s.providerChain, s.path, ccv.ProviderPortID, s.path.EndpointB.ChannelID, 1)

	//reward for the provider chain will be sent after each 2 blocks
	consumerParams := s.consumerChain.App.(*app.App).GetSubspace(consumertypes.ModuleName)
	consumerParams.Set(s.consumerCtx(), consumertypes.KeyBlocksPerDistributionTransmission, int64(2))
	s.consumerChain.NextBlock()

	consumerAccountKeeper := s.consumerChain.App.(*app.App).AccountKeeper
	consumerBankKeeper := s.consumerChain.App.(*app.App).BankKeeper

	//send coins to the fee pool which is used for reward distribution
	consumerFeePoolAddr := consumerAccountKeeper.GetModuleAccount(s.consumerCtx(), authtypes.FeeCollectorName).GetAddress()
	feePoolTokensOld := consumerBankKeeper.GetAllBalances(s.consumerCtx(), consumerFeePoolAddr)
	fees := sdk.NewCoins(sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(100)))
	err := consumerBankKeeper.SendCoinsFromAccountToModule(s.consumerCtx(), s.consumerChain.SenderAccount.GetAddress(), authtypes.FeeCollectorName, fees)
	s.Require().NoError(err)
	feePoolTokens := consumerBankKeeper.GetAllBalances(s.consumerCtx(), consumerFeePoolAddr)
	s.Require().Equal(sdk.NewInt(100).Add(feePoolTokensOld.AmountOf(sdk.DefaultBondDenom)), feePoolTokens.AmountOf(sdk.DefaultBondDenom))

	//calculate the reward for consumer and provider chain. Consumer will receive ConsumerRedistributeFrac, the rest is going to provider
	frac, err := sdk.NewDecFromStr(consumerkeeper.ConsumerRedistributeFrac)
	s.Require().NoError(err)
	consumerExpectedRewards, _ := sdk.NewDecCoinsFromCoins(feePoolTokens...).MulDec(frac).TruncateDecimal()
	providerExpectedRewards := feePoolTokens.Sub(consumerExpectedRewards)
	s.consumerChain.NextBlock()

	//amount from the fee pool is devided between consumer redistribute address and address reserved for provider chain
	feePoolTokens = consumerBankKeeper.GetAllBalances(s.consumerCtx(), consumerFeePoolAddr)
	s.Require().Equal(0, len(feePoolTokens))
	consumerRedistributeAddr := consumerAccountKeeper.GetModuleAccount(s.consumerCtx(), consumertypes.ConsumerRedistributeName).GetAddress()
	consumerTokens := consumerBankKeeper.GetAllBalances(s.consumerCtx(), consumerRedistributeAddr)
	s.Require().Equal(consumerExpectedRewards.AmountOf(sdk.DefaultBondDenom), consumerTokens.AmountOf(sdk.DefaultBondDenom))
	providerRedistributeAddr := consumerAccountKeeper.GetModuleAccount(s.consumerCtx(), consumertypes.SendToProviderName).GetAddress()
	providerTokens := consumerBankKeeper.GetAllBalances(s.consumerCtx(), providerRedistributeAddr)
	s.Require().Equal(providerExpectedRewards.AmountOf(sdk.DefaultBondDenom), providerTokens.AmountOf(sdk.DefaultBondDenom))

	//send the reward to provider chain after 2 blocks
	s.consumerChain.NextBlock()
	providerTokens = consumerBankKeeper.GetAllBalances(s.consumerCtx(), providerRedistributeAddr)
	s.Require().Equal(0, len(providerTokens))

	relayAllCommittedPackets(s, s.consumerChain, s.transferPath, transfertypes.PortID, s.transferPath.EndpointA.ChannelID, 1)
	s.providerChain.NextBlock()
	communityCoins := s.providerChain.App.(*providerApp.App).DistrKeeper.GetFeePoolCommunityCoins(s.providerCtx())
	ibcCoinIndex := -1
	for i, coin := range communityCoins {
		if strings.HasPrefix(coin.Denom, "ibc") {
			ibcCoinIndex = i
		}
	}
	s.Require().Greater(ibcCoinIndex, -1)
	s.Require().True(communityCoins[ibcCoinIndex].Amount.Equal(sdk.NewDecCoinFromCoin(providerExpectedRewards[0]).Amount))
}
