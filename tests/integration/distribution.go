package integration

import (
	"strings"

	sdk "github.com/cosmos/cosmos-sdk/types"
	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"
	transfertypes "github.com/cosmos/ibc-go/v7/modules/apps/transfer/types"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
)

// This test is valid for minimal viable consumer chain
func (s *CCVTestSuite) TestRewardsDistribution() {
	// set up channel and delegate some tokens in order for validator set update to be sent to the consumer chain
	s.SetupCCVChannel(s.path)
	s.SetupTransferChannel()
	bondAmt := sdk.NewInt(10000000)
	delAddr := s.providerChain.SenderAccount.GetAddress()
	delegate(s, delAddr, bondAmt)
	s.providerChain.NextBlock()

	// relay VSC packets from provider to consumer
	relayAllCommittedPackets(s, s.providerChain, s.path, ccv.ProviderPortID, s.path.EndpointB.ChannelID, 1)

	// reward for the provider chain will be sent after each 2 blocks
	consumerParams := s.consumerApp.GetSubspace(consumertypes.ModuleName)
	consumerParams.Set(s.consumerCtx(), consumertypes.KeyBlocksPerDistributionTransmission, int64(2))
	s.consumerChain.NextBlock()

	consumerAccountKeeper := s.consumerApp.GetTestAccountKeeper()
	consumerBankKeeper := s.consumerApp.GetTestBankKeeper()

	// send coins to the fee pool which is used for reward distribution
	consumerFeePoolAddr := consumerAccountKeeper.GetModuleAccount(s.consumerCtx(), authtypes.FeeCollectorName).GetAddress()
	feePoolTokensOld := consumerBankKeeper.GetAllBalances(s.consumerCtx(), consumerFeePoolAddr)
	fees := sdk.NewCoins(sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(100)))
	err := consumerBankKeeper.SendCoinsFromAccountToModule(s.consumerCtx(), s.consumerChain.SenderAccount.GetAddress(), authtypes.FeeCollectorName, fees)
	s.Require().NoError(err)
	feePoolTokens := consumerBankKeeper.GetAllBalances(s.consumerCtx(), consumerFeePoolAddr)
	s.Require().Equal(sdk.NewInt(100).Add(feePoolTokensOld.AmountOf(sdk.DefaultBondDenom)), feePoolTokens.AmountOf(sdk.DefaultBondDenom))

	// calculate the reward for consumer and provider chain. Consumer will receive ConsumerRedistributeFrac, the rest is going to provider
	frac, err := sdk.NewDecFromStr(s.consumerApp.GetConsumerKeeper().GetConsumerRedistributionFrac(s.consumerCtx()))
	s.Require().NoError(err)
	consumerExpectedRewards, _ := sdk.NewDecCoinsFromCoins(feePoolTokens...).MulDec(frac).TruncateDecimal()
	providerExpectedRewards := feePoolTokens.Sub(consumerExpectedRewards...)
	s.consumerChain.NextBlock()

	// amount from the fee pool is divided between consumer redistribute address and address reserved for provider chain
	feePoolTokens = consumerBankKeeper.GetAllBalances(s.consumerCtx(), consumerFeePoolAddr)
	s.Require().Equal(0, len(feePoolTokens))
	consumerRedistributeAddr := consumerAccountKeeper.GetModuleAccount(s.consumerCtx(), consumertypes.ConsumerRedistributeName).GetAddress()
	consumerTokens := consumerBankKeeper.GetAllBalances(s.consumerCtx(), consumerRedistributeAddr)
	s.Require().Equal(consumerExpectedRewards.AmountOf(sdk.DefaultBondDenom), consumerTokens.AmountOf(sdk.DefaultBondDenom))
	providerRedistributeAddr := consumerAccountKeeper.GetModuleAccount(s.consumerCtx(), consumertypes.ConsumerToSendToProviderName).GetAddress()
	providerTokens := consumerBankKeeper.GetAllBalances(s.consumerCtx(), providerRedistributeAddr)
	s.Require().Equal(providerExpectedRewards.AmountOf(sdk.DefaultBondDenom), providerTokens.AmountOf(sdk.DefaultBondDenom))

	// send the reward to provider chain after 2 blocks

	s.consumerChain.NextBlock()
	providerTokens = consumerBankKeeper.GetAllBalances(s.consumerCtx(), providerRedistributeAddr)
	s.Require().Equal(0, len(providerTokens))

	relayAllCommittedPackets(s, s.consumerChain, s.transferPath, transfertypes.PortID, s.transferPath.EndpointA.ChannelID, 1)
	s.providerChain.NextBlock()
	communityCoins := s.providerApp.GetTestDistributionKeeper().GetFeePoolCommunityCoins(s.providerCtx())
	ibcCoinIndex := -1
	for i, coin := range communityCoins {
		if strings.HasPrefix(coin.Denom, "ibc") {
			ibcCoinIndex = i
		}
	}
	s.Require().Greater(ibcCoinIndex, -1)
	s.Require().True(communityCoins[ibcCoinIndex].Amount.Equal(sdk.NewDecCoinFromCoin(providerExpectedRewards[0]).Amount))
}

// TestSendRewardsRetries tests that failed reward transmissions are retried every BlocksPerDistributionTransmission blocks
func (s *CCVTestSuite) TestSendRewardsRetries() {
	// TODO: this setup can be consolidated with other tests in the file

	// ccv and transmission channels setup
	s.SetupCCVChannel(s.path)
	s.SetupTransferChannel()
	bondAmt := sdk.NewInt(10000000)
	delAddr := s.providerChain.SenderAccount.GetAddress()
	delegate(s, delAddr, bondAmt)
	s.providerChain.NextBlock()

	// relay VSC packets from provider to consumer
	relayAllCommittedPackets(s, s.providerChain, s.path, ccv.ProviderPortID, s.path.EndpointB.ChannelID, 1)

	consumerBankKeeper := s.consumerApp.GetTestBankKeeper()
	consumerKeeper := s.consumerApp.GetConsumerKeeper()

	// reward for the provider chain will be sent after each 1000 blocks
	consumerParams := s.consumerApp.GetSubspace(consumertypes.ModuleName)
	consumerParams.Set(s.consumerCtx(), consumertypes.KeyBlocksPerDistributionTransmission, int64(1000))

	// fill fee pool
	fees := sdk.NewCoins(sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(100)))
	err := consumerBankKeeper.SendCoinsFromAccountToModule(s.consumerCtx(),
		s.consumerChain.SenderAccount.GetAddress(), authtypes.FeeCollectorName, fees)
	s.Require().NoError(err)

	// Corrupt transmission channel, confirm escrow balance is not updated
	// when reward dist is attempted, but LTBH is updated
	oldEscBalance := s.getEscrowBalance()
	oldLbth := consumerKeeper.GetLastTransmissionBlockHeight(s.consumerCtx())
	s.corruptTransChannel()
	s.prepareRewardDist()
	s.consumerChain.NextBlock()
	newEscBalance := s.getEscrowBalance()
	s.Require().Equal(oldEscBalance, newEscBalance,
		"expected escrow balance to NOT BE updated - OLD: %s, NEW: %s", oldEscBalance, newEscBalance)
	newLbth := consumerKeeper.GetLastTransmissionBlockHeight(s.consumerCtx())
	s.Require().Equal(oldLbth.Height+consumerKeeper.GetBlocksPerDistributionTransmission(s.consumerCtx()), newLbth.Height,
		"expected new LTBH to be previous value + blocks per dist transmission")

	// Prepare reward distribution again, confirm escrow balance is still not updated, but LTBH is updated
	oldEscBalance = s.getEscrowBalance()
	oldLbth = consumerKeeper.GetLastTransmissionBlockHeight(s.consumerCtx())
	s.prepareRewardDist()
	s.consumerChain.NextBlock()
	newEscBalance = s.getEscrowBalance()
	s.Require().Equal(oldEscBalance, newEscBalance,
		"expected escrow balance to NOT BE updated - OLD: %s, NEW: %s", oldEscBalance, newEscBalance)
	newLbth = consumerKeeper.GetLastTransmissionBlockHeight(s.consumerCtx())
	s.Require().Equal(oldLbth.Height+consumerKeeper.GetBlocksPerDistributionTransmission(s.consumerCtx()), newLbth.Height,
		"expected new LTBH to be previous value + blocks per dist transmission")

	// Now fix transmission channel, confirm escrow balance is updated upon reward distribution
	transChanID := s.consumerApp.GetConsumerKeeper().GetDistributionTransmissionChannel(s.consumerCtx())
	tChan, _ := s.consumerApp.GetIBCKeeper().ChannelKeeper.GetChannel(s.consumerCtx(), transfertypes.PortID, transChanID)
	tChan.Counterparty.PortId = transfertypes.PortID
	s.consumerApp.GetIBCKeeper().ChannelKeeper.SetChannel(s.consumerCtx(), transfertypes.PortID, transChanID, tChan)

	oldEscBalance = s.getEscrowBalance()
	s.prepareRewardDist()
	s.consumerChain.NextBlock()
	newEscBalance = s.getEscrowBalance()
	s.Require().NotEqual(oldEscBalance, newEscBalance,
		"expected escrow balance to BE updated - OLD: %s, NEW: %s", oldEscBalance, newEscBalance)
}

// TestEndBlockRD tests that the last transmission block height (LTBH) is correctly updated after the expected
// number of block have passed. It also checks that the IBC transfer transfer states are discarded if
// the reward distribution to the provider has failed.
//
// Note: this method is effectively a unit test for EndBLockRD(), but is written as an integration test to avoid excessive mocking.
func (s *CCVTestSuite) TestEndBlockRD() {
	testCases := []struct {
		name                    string
		prepareRewardDist       bool
		corruptTransChannel     bool
		expLBThUpdated          bool
		expEscrowBalanceChanged bool
	}{
		{
			name:                    "should not update LBTH before blocks per dist trans block are passed",
			prepareRewardDist:       false,
			corruptTransChannel:     false,
			expLBThUpdated:          false,
			expEscrowBalanceChanged: false,
		},
		{
			name:                    "should update LBTH when blocks per dist trans or more block are passed",
			prepareRewardDist:       true,
			corruptTransChannel:     false,
			expLBThUpdated:          true,
			expEscrowBalanceChanged: true,
		},
		{
			name:                    "should update LBTH and discard the IBC transfer states when sending rewards to provider fails",
			prepareRewardDist:       true,
			corruptTransChannel:     true,
			expLBThUpdated:          true,
			expEscrowBalanceChanged: false,
		},
	}

	for _, tc := range testCases {

		s.SetupTest()

		// ccv and transmission channels setup
		s.SetupCCVChannel(s.path)
		s.SetupTransferChannel()
		bondAmt := sdk.NewInt(10000000)
		delAddr := s.providerChain.SenderAccount.GetAddress()
		delegate(s, delAddr, bondAmt)
		s.providerChain.NextBlock()

		// relay VSC packets from provider to consumer
		relayAllCommittedPackets(s, s.providerChain, s.path, ccv.ProviderPortID, s.path.EndpointB.ChannelID, 1)

		consumerKeeper := s.consumerApp.GetConsumerKeeper()
		consumerBankKeeper := s.consumerApp.GetTestBankKeeper()

		// reward for the provider chain will be sent after each 1000 blocks
		consumerParams := s.consumerApp.GetSubspace(consumertypes.ModuleName)
		consumerParams.Set(s.consumerCtx(), consumertypes.KeyBlocksPerDistributionTransmission, int64(1000))

		// fill fee pool
		fees := sdk.NewCoins(sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(100)))
		err := consumerBankKeeper.SendCoinsFromAccountToModule(s.consumerCtx(),
			s.consumerChain.SenderAccount.GetAddress(), authtypes.FeeCollectorName, fees)
		s.Require().NoError(err)

		oldLbth := consumerKeeper.GetLastTransmissionBlockHeight(s.consumerCtx())
		oldEscBalance := s.getEscrowBalance()

		if tc.prepareRewardDist {
			s.prepareRewardDist()
		}

		if tc.corruptTransChannel {
			s.corruptTransChannel()
		}

		s.consumerChain.NextBlock()

		if tc.expLBThUpdated {
			lbth := consumerKeeper.GetLastTransmissionBlockHeight(s.consumerCtx())
			// checks that the current LBTH is greater than the old one
			s.Require().True(oldLbth.Height < lbth.Height)
			// confirm the LBTH was updated during the most recently executed block
			s.Require().Equal(s.consumerCtx().BlockHeight()-1, lbth.Height)
		}

		currentEscrowBalance := s.getEscrowBalance()
		if tc.expEscrowBalanceChanged {
			// check that the coins present on the escrow account balance are updated
			s.Require().NotEqual(currentEscrowBalance, oldEscBalance,
				"expected escrow balance to BE updated - OLD: %s, NEW: %s", oldEscBalance, currentEscrowBalance)
		} else {
			// check that the coins present on the escrow account balance aren't updated
			s.Require().Equal(currentEscrowBalance, oldEscBalance,
				"expected escrow balance to NOT BE updated - OLD: %s, NEW: %s", oldEscBalance, currentEscrowBalance)
		}
	}
}

// getEscrowBalance gets the current balances in the escrow account holding the transferred tokens to the provider
func (s CCVTestSuite) getEscrowBalance() sdk.Coins { //nolint:govet // we copy locks for this test
	consumerBankKeeper := s.consumerApp.GetTestBankKeeper()
	transChanID := s.consumerApp.GetConsumerKeeper().GetDistributionTransmissionChannel(s.consumerCtx())
	escAddr := transfertypes.GetEscrowAddress(transfertypes.PortID, transChanID)
	return consumerBankKeeper.GetAllBalances(s.consumerCtx(), escAddr)
}

// corruptTransChannel intentionally causes the reward distribution to fail by corrupting the transmission,
// causing the SendPacket function to return an error.
// Note that the Transferkeeper sends the outgoing fees to an escrow address BEFORE the reward distribution
// is aborted within the SendPacket function.
func (s *CCVTestSuite) corruptTransChannel() {
	transChanID := s.consumerApp.GetConsumerKeeper().GetDistributionTransmissionChannel(s.consumerCtx())
	tChan, _ := s.consumerApp.GetIBCKeeper().ChannelKeeper.GetChannel(
		s.consumerCtx(), transfertypes.PortID, transChanID)
	tChan.Counterparty.PortId = "invalid/PortID"
	s.consumerApp.GetIBCKeeper().ChannelKeeper.SetChannel(
		s.consumerCtx(), transfertypes.PortID, transChanID, tChan)
}

// prepareRewardDist passes enough blocks so that a reward distribution is triggered in the next consumer EndBlock
func (s *CCVTestSuite) prepareRewardDist() {
	consumerKeeper := s.consumerApp.GetConsumerKeeper()
	bpdt := consumerKeeper.GetBlocksPerDistributionTransmission(s.consumerCtx())
	currentHeight := s.consumerCtx().BlockHeight()
	lastTransHeight := consumerKeeper.GetLastTransmissionBlockHeight(s.consumerCtx())
	blocksSinceLastTrans := currentHeight - lastTransHeight.Height
	blocksToGo := bpdt - blocksSinceLastTrans
	s.coordinator.CommitNBlocks(s.consumerChain, uint64(blocksToGo))
}
