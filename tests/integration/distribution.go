package integration

import (
	"fmt"
	"strings"

	abci "github.com/cometbft/cometbft/abci/types"
	transfertypes "github.com/cosmos/ibc-go/v7/modules/apps/transfer/types"

	sdk "github.com/cosmos/cosmos-sdk/types"
	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"

	icstestingutils "github.com/cosmos/interchain-security/v4/testutil/integration"
	consumerkeeper "github.com/cosmos/interchain-security/v4/x/ccv/consumer/keeper"
	consumertypes "github.com/cosmos/interchain-security/v4/x/ccv/consumer/types"
	ccv "github.com/cosmos/interchain-security/v4/x/ccv/types"
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

	// register a consumer reward denom
	params := s.consumerApp.GetConsumerKeeper().GetConsumerParams(s.consumerCtx())
	params.RewardDenoms = []string{sdk.DefaultBondDenom}
	s.consumerApp.GetConsumerKeeper().SetParams(s.consumerCtx(), params)

	// relay VSC packets from provider to consumer
	relayAllCommittedPackets(s, s.providerChain, s.path, ccv.ProviderPortID, s.path.EndpointB.ChannelID, 1)

	// reward for the provider chain will be sent after each 2 blocks
	consumerParams := s.consumerApp.GetSubspace(consumertypes.ModuleName)
	consumerParams.Set(s.consumerCtx(), ccv.KeyBlocksPerDistributionTransmission, int64(2))
	s.consumerChain.NextBlock()

	consumerAccountKeeper := s.consumerApp.GetTestAccountKeeper()
	consumerBankKeeper := s.consumerApp.GetTestBankKeeper()
	providerBankKeeper := s.providerApp.GetTestBankKeeper()

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

	// Since consumer reward denom is not yet registered, the coins never get into the fee pool, staying in the ConsumerRewardsPool
	rewardPoolAddrs := s.providerApp.GetProviderKeeper().GetConsumerModuleAccountAddress(s.providerCtx(), s.consumerChain.ChainID)
	rewardCoins := providerBankKeeper.GetAllBalances(s.providerCtx(), rewardPoolAddrs)

	ibcCoinIndex := -1
	for i, coin := range rewardCoins {
		if strings.HasPrefix(coin.Denom, "ibc") {
			ibcCoinIndex = i
		}
	}

	// Check that we found an ibc denom in the reward pool
	s.Require().Greater(ibcCoinIndex, -1)

	// Check that the coins got into the ConsumerRewardsPool
	s.Require().True(rewardCoins[ibcCoinIndex].Amount.Equal(providerExpectedRewards[0].Amount))

	// Advance a block and check that the coins are still in the ConsumerRewardsPool
	s.providerChain.NextBlock()
	rewardCoins = providerBankKeeper.GetAllBalances(s.providerCtx(), rewardPoolAddrs)
	s.Require().True(rewardCoins[ibcCoinIndex].Amount.Equal(providerExpectedRewards[0].Amount))

	// Set the consumer reward denom. This would be done by a governance proposal in prod
	s.providerApp.GetProviderKeeper().SetConsumerRewardDenom(s.providerCtx(), rewardCoins[ibcCoinIndex].Denom)

	s.providerChain.NextBlock()

	// Check that the reward pool has no more coins because they were transferred to the fee pool
	rewardCoins = providerBankKeeper.GetAllBalances(s.providerCtx(), rewardPoolAddrs)
	s.Require().Equal(0, len(rewardCoins))

	// check that the fee pool has the expected amount of coins
	communityCoins := s.providerApp.GetTestDistributionKeeper().GetFeePoolCommunityCoins(s.providerCtx())
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

	// Register denom on consumer chain
	params := s.consumerApp.GetConsumerKeeper().GetConsumerParams(s.consumerCtx())
	params.RewardDenoms = []string{sdk.DefaultBondDenom}
	s.consumerApp.GetConsumerKeeper().SetParams(s.consumerCtx(), params)

	// relay VSC packets from provider to consumer
	relayAllCommittedPackets(s, s.providerChain, s.path, ccv.ProviderPortID, s.path.EndpointB.ChannelID, 1)

	consumerBankKeeper := s.consumerApp.GetTestBankKeeper()
	consumerKeeper := s.consumerApp.GetConsumerKeeper()

	// reward for the provider chain will be sent after each 1000 blocks
	consumerParams := s.consumerApp.GetSubspace(consumertypes.ModuleName)
	consumerParams.Set(s.consumerCtx(), ccv.KeyBlocksPerDistributionTransmission, int64(1000))

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
		denomRegistered         bool
	}{
		{
			name:                    "should not update LBTH before blocks per dist trans block are passed",
			prepareRewardDist:       false,
			corruptTransChannel:     false,
			expLBThUpdated:          false,
			denomRegistered:         true,
			expEscrowBalanceChanged: false,
		},
		{
			name:                    "should update LBTH when blocks per dist trans or more block are passed",
			prepareRewardDist:       true,
			corruptTransChannel:     false,
			expLBThUpdated:          true,
			denomRegistered:         true,
			expEscrowBalanceChanged: true,
		},
		{
			name:                    "should update LBTH and discard the IBC transfer states when sending rewards to provider fails",
			prepareRewardDist:       true,
			corruptTransChannel:     true,
			expLBThUpdated:          true,
			denomRegistered:         true,
			expEscrowBalanceChanged: false,
		},
		{
			name:                    "should not change escrow balance when denom is not registered",
			prepareRewardDist:       true,
			corruptTransChannel:     false,
			expLBThUpdated:          true,
			denomRegistered:         false,
			expEscrowBalanceChanged: false,
		},
		{
			name:                    "should change escrow balance when denom is registered",
			prepareRewardDist:       true,
			corruptTransChannel:     false,
			expLBThUpdated:          true,
			denomRegistered:         true,
			expEscrowBalanceChanged: true,
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

		if tc.denomRegistered {
			params := s.consumerApp.GetConsumerKeeper().GetConsumerParams(s.consumerCtx())
			params.RewardDenoms = []string{sdk.DefaultBondDenom}
			s.consumerApp.GetConsumerKeeper().SetParams(s.consumerCtx(), params)
		}

		// relay VSC packets from provider to consumer
		relayAllCommittedPackets(s, s.providerChain, s.path, ccv.ProviderPortID, s.path.EndpointB.ChannelID, 1)

		consumerKeeper := s.consumerApp.GetConsumerKeeper()
		consumerBankKeeper := s.consumerApp.GetTestBankKeeper()

		// reward for the provider chain will be sent after each 1000 blocks
		consumerParams := s.consumerApp.GetSubspace(consumertypes.ModuleName)
		consumerParams.Set(s.consumerCtx(), ccv.KeyBlocksPerDistributionTransmission, int64(1000))

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

// TestSendRewardsToProvider is effectively a unit test for SendRewardsToProvider(),
// but is written as an integration test to avoid excessive mocking.
func (s *CCVTestSuite) TestSendRewardsToProvider() {
	testCases := []struct {
		name           string
		setup          func(sdk.Context, *consumerkeeper.Keeper, icstestingutils.TestBankKeeper)
		expError       bool
		tokenTransfers int
	}{
		{
			name: "successful token transfer",
			setup: func(ctx sdk.Context, keeper *consumerkeeper.Keeper, bankKeeper icstestingutils.TestBankKeeper) {
				s.SetupTransferChannel()

				// register a consumer reward denom
				params := keeper.GetConsumerParams(ctx)
				params.RewardDenoms = []string{sdk.DefaultBondDenom}
				keeper.SetParams(ctx, params)

				// send coins to the pool which is used for collect reward distributions to be sent to the provider
				err := bankKeeper.SendCoinsFromAccountToModule(
					ctx,
					s.consumerChain.SenderAccount.GetAddress(),
					consumertypes.ConsumerToSendToProviderName,
					sdk.NewCoins(sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(100))),
				)
				s.Require().NoError(err)
			},
			expError:       false,
			tokenTransfers: 1,
		},
		{
			name: "no transfer channel",
			setup: func(ctx sdk.Context, keeper *consumerkeeper.Keeper, bankKeeper icstestingutils.TestBankKeeper) {
			},
			expError:       false,
			tokenTransfers: 0,
		},
		{
			name: "no reward denom",
			setup: func(ctx sdk.Context, keeper *consumerkeeper.Keeper, bankKeeper icstestingutils.TestBankKeeper) {
				s.SetupTransferChannel()
			},
			expError:       false,
			tokenTransfers: 0,
		},
		{
			name: "reward balance is zero",
			setup: func(ctx sdk.Context, keeper *consumerkeeper.Keeper, bankKeeper icstestingutils.TestBankKeeper) {
				s.SetupTransferChannel()

				// register a consumer reward denom
				params := keeper.GetConsumerParams(ctx)
				params.RewardDenoms = []string{"uatom"}
				keeper.SetParams(ctx, params)

				denoms := keeper.AllowedRewardDenoms(ctx)
				s.Require().Len(denoms, 1)
			},
			expError:       false,
			tokenTransfers: 0,
		},
		{
			name: "no distribution transmission channel",
			setup: func(ctx sdk.Context, keeper *consumerkeeper.Keeper, bankKeeper icstestingutils.TestBankKeeper) {
				s.SetupTransferChannel()

				// register a consumer reward denom
				params := keeper.GetConsumerParams(ctx)
				params.RewardDenoms = []string{sdk.DefaultBondDenom}
				params.DistributionTransmissionChannel = ""
				keeper.SetParams(ctx, params)

				// send coins to the pool which is used for collect reward distributions to be sent to the provider
				err := bankKeeper.SendCoinsFromAccountToModule(
					ctx,
					s.consumerChain.SenderAccount.GetAddress(),
					consumertypes.ConsumerToSendToProviderName,
					sdk.NewCoins(sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(100))),
				)
				s.Require().NoError(err)
			},
			expError:       false,
			tokenTransfers: 0,
		},
		{
			name: "no recipient address",
			setup: func(ctx sdk.Context, keeper *consumerkeeper.Keeper, bankKeeper icstestingutils.TestBankKeeper) {
				s.SetupTransferChannel()

				// register a consumer reward denom
				params := keeper.GetConsumerParams(ctx)
				params.RewardDenoms = []string{sdk.DefaultBondDenom}
				params.ProviderFeePoolAddrStr = ""
				keeper.SetParams(ctx, params)

				// send coins to the pool which is used for collect reward distributions to be sent to the provider
				err := bankKeeper.SendCoinsFromAccountToModule(
					ctx,
					s.consumerChain.SenderAccount.GetAddress(),
					consumertypes.ConsumerToSendToProviderName,
					sdk.NewCoins(sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(100))),
				)
				s.Require().NoError(err)
			},
			expError:       true,
			tokenTransfers: 0,
		},
	}

	for _, tc := range testCases {
		s.SetupTest()

		// ccv channels setup
		s.SetupCCVChannel(s.path)
		bondAmt := sdk.NewInt(10000000)
		delAddr := s.providerChain.SenderAccount.GetAddress()
		delegate(s, delAddr, bondAmt)
		s.providerChain.NextBlock()

		// customized setup
		consumerCtx := s.consumerCtx()
		consumerKeeper := s.consumerApp.GetConsumerKeeper()
		tc.setup(consumerCtx, &consumerKeeper, s.consumerApp.GetTestBankKeeper())

		// call SendRewardsToProvider
		err := s.consumerApp.GetConsumerKeeper().SendRewardsToProvider(consumerCtx)
		if tc.expError {
			s.Require().Error(err)
		} else {
			s.Require().NoError(err)
		}

		// check whether the amount of token transfers is as expected
		commitments := s.consumerApp.GetIBCKeeper().ChannelKeeper.GetAllPacketCommitmentsAtChannel(
			consumerCtx,
			transfertypes.PortID,
			s.consumerApp.GetConsumerKeeper().GetDistributionTransmissionChannel(consumerCtx),
		)
		s.Require().Len(commitments, tc.tokenTransfers, "unexpected amount of token transfers; test: %s", tc.name)
	}
}

// getEscrowBalance gets the current balances in the escrow account holding the transferred tokens to the provider
func (s *CCVTestSuite) getEscrowBalance() sdk.Coins {
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

// This test is valid for minimal viable consumer chain
func (s *CCVTestSuite) TestAllocateTokens() {
	// set up channel and delegate some tokens in order for validator set update to be sent to the consumer chain
	s.SetupAllCCVChannels()
	providerKeeper := s.providerApp.GetProviderKeeper()
	acountKeeper := s.providerApp.GetTestAccountKeeper()
	bankKeeper := s.providerApp.GetTestBankKeeper()
	distributionKeeper := s.providerApp.GetTestDistributionKeeper()

	// consumerkeeper := s.consumerApp.GetConsumerKeeper()
	chainRewardPools := map[string]authtypes.AccountI{}
	for chainID, chain := range s.consumerBundles {
		accName := providerKeeper.GetConsumerModuleAccount(s.providerCtx(), chainID)
		acc := acountKeeper.GetModuleAccount(s.providerCtx(), accName)
		// verify consumer gets the expected module account address
		// after the CCV handshake
		s.Require().Equal(
			acc.GetAddress().String(),
			chain.App.GetConsumerKeeper().GetProviderFeePoolAddrStr(chain.GetCtx()),
		)

		chainRewardPools[accName] = acc
	}

	providerKeeper.SetConsumerRewardDenom(s.providerCtx(), sdk.DefaultBondDenom) // register a consumer reward denom

	// TEST BEGINBLOCKRD
	delAddr := s.providerChain.SenderAccount.GetAddress()
	baseFee := sdk.NewCoins(sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(100)))

	// fund consumer reward pools
	for rp := range chainRewardPools {
		bankKeeper.SendCoinsFromAccountToModule(
			s.providerCtx(),
			delAddr,
			rp,
			baseFee,
		)
	}

	// Create vote since the ibctesting NextBlock() doesn't
	// implement abci votes

	votes := []abci.VoteInfo{}
	for _, val := range s.providerChain.Vals.Validators {
		votes = append(votes,
			abci.VoteInfo{
				Validator:       abci.Validator{Address: val.Address, Power: val.VotingPower},
				SignedLastBlock: true,
			},
		)

		valReward := distributionKeeper.GetValidatorOutstandingRewards(s.providerCtx(), sdk.ValAddress(val.Address))
		fmt.Println("val outstanding reward: ", valReward.String())
	}

	for _, acc := range chainRewardPools {
		bal := bankKeeper.GetAllBalances(
			s.providerCtx(),
			acc.GetAddress(),
		)
		fmt.Println("balance :", bal)
	}

	fmt.Println("community pool balance: ", distributionKeeper.GetFeePoolCommunityCoins(s.providerCtx()))

	fmt.Println("-----------Provider BeginBlock--------------")

	providerKeeper.BeginBlockRD(
		s.providerCtx(),
		abci.RequestBeginBlock{
			LastCommitInfo: abci.CommitInfo{
				Votes: votes,
			},
		},
	)

	for _, acc := range chainRewardPools {
		bal := bankKeeper.GetAllBalances(
			s.providerCtx(),
			acc.GetAddress(),
		)
		fmt.Println("balance: ", bal)
	}

	for _, val := range s.providerChain.Vals.Validators {

		valReward := distributionKeeper.GetValidatorOutstandingRewards(s.providerCtx(), sdk.ValAddress(val.Address))
		fmt.Println("val outstanding reward: ", valReward.String())
	}

	fmt.Println("community pool balance: ", distributionKeeper.GetFeePoolCommunityCoins(s.providerCtx()))

	// // // register a consumer reward denom
	// // params := s.consumerApp.GetConsumerKeeper().GetConsumerParams(s.consumerCtx())
	// // params.RewardDenoms = []string{sdk.DefaultBondDenom}
	// // s.consumerApp.GetConsumerKeeper().SetParams(s.consumerCtx(), params)

	// // set module account for consumer chain 1
	// providerKeeper := s.providerApp.GetProviderKeeper()
	// // acountKeeper := s.providerApp.GetTestAccountKeeper()
	// bankKeeper := s.providerApp.GetTestBankKeeper()

	// // consuModAcct0 := acountKeeper.GetModuleAccount(s.providerCtx(), types.ConsumerRewardsPool0)
	// // consuModAcct1 := acountKeeper.GetModuleAccount(s.providerCtx(), types.ConsumerRewardsPool1)
	// // consuModAcct2 := acountKeeper.GetModuleAccount(s.providerCtx(), types.ConsumerRewardsPool2)

	// consuModAcctNames := []string{
	// 	// types.ConsumerRewardsPool0,
	// 	// types.ConsumerRewardsPool1,
	// 	// types.ConsumerRewardsPool2,
	// }

	// baseFee := sdk.NewCoins(sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(100)))
	// delAddr := s.providerChain.SenderAccount.GetAddress()
	// validators := s.providerChain.Vals.Validators

	// providerKeeper.SetConsumerRewardDenom(s.providerCtx(), sdk.DefaultBondDenom) // // register a consumer reward denom
	// // params := s.consumerApp.GetConsumerKeeper().GetConsumerParams(s.consumerCtx())
	// // params.RewardDenoms = []string{sdk.DefaultBondDenom}
	// // s.consumerApp.GetConsumerKeeper().SetParams(s.consumerCtx(), params))

	// for i := 0; i < 3; i++ {
	// 	fee := baseFee.Add(sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(int64(i))))

	// 	bankKeeper.SendCoinsFromAccountToModule(
	// 		s.providerCtx(),
	// 		delAddr,
	// 		consuModAcctNames[i],
	// 		fee,
	// 	)

	// 	s.Require().True(
	// 		fee.IsEqual(
	// 			bankKeeper.GetAllBalances(
	// 				s.providerCtx(),
	// 				authtypes.NewModuleAddress(consuModAcctNames[i]),
	// 			),
	// 		),
	// 	)

	// 	// first consumer has all the validators optIn already (preProposalKeyAssignment)
	// 	if i > 0 {
	// 		val := validators[i]
	// 		chainID := s.consumerBundles["testchain"+strconv.Itoa(i+2)].Chain.ChainID // DIRTY
	// 		// get SDK validator
	// 		valAddr, err := sdk.ValAddressFromHex(val.Address.String())
	// 		s.Require().NoError(err)
	// 		validator := s.getVal(s.providerCtx(), valAddr)

	// 		// generate new PrivValidator
	// 		privVal := mock.NewPV()
	// 		tmPubKey, err := privVal.GetPubKey()
	// 		s.Require().NoError(err)
	// 		consumerKey, err := tmencoding.PubKeyToProto(tmPubKey)
	// 		s.Require().NoError(err)

	// 		// add Signer to the provider chain as there is no consumer chain to add it;
	// 		// as a result, NewTestChainWithValSet in AddConsumer uses providerChain.Signers
	// 		s.providerChain.Signers[tmPubKey.Address().String()] = privVal

	// 		err = providerKeeper.AssignConsumerKey(s.providerCtx(), chainID, validator, consumerKey)
	// 		s.Require().NoError(err)
	// 	}

	// 	valOldBal := map[string]sdk.DecCoins{}
	// 	votes := []abci.VoteInfo{}

	// 	for _, val := range validators {
	// 		valAddr, err := sdk.ValAddressFromHex(val.Address.String())
	// 		s.Require().NoError(err)
	// 		valOldBal[valAddr.String()] = s.providerApp.GetTestDistributionKeeper().GetValidatorOutstandingRewards(s.providerCtx(), valAddr).Rewards
	// 		votes = append(votes,
	// 			abci.VoteInfo{
	// 				Validator:       abci.Validator{Address: val.Address, Power: val.VotingPower},
	// 				SignedLastBlock: true,
	// 			},
	// 		)
	// 	}

	// 	providerKeeper.AllocateTokens(s.providerCtx(), s.providerChain.Vals.TotalVotingPower(), votes)

	// 	// s.providerChain.LastHeader.ValidatorSet.TotalVotingPower

	// 	for _, val := range validators {
	// 		valAddr, err := sdk.ValAddressFromHex(val.Address.String())
	// 		s.Require().NoError(err)
	// 		valOldBal[valAddr.String()] = s.providerApp.GetTestDistributionKeeper().GetValidatorOutstandingRewards(s.providerCtx(), valAddr).Rewards
	// 	}

	// }

	// fmt.Println(providerKeeper.GetAllValidatorConsumerPubKeys(s.providerCtx(), &s.consumerChain.ChainID))
	// fmt.Println(providerKeeper.GetAllValidatorConsumerPubKeys(s.providerCtx(), &(s.consumerBundles["testchain3"].Chain.ChainID)))
	// fmt.Println(providerKeeper.GetAllValidatorConsumerPubKeys(s.providerCtx(), &(s.consumerBundles["testchain4"].Chain.ChainID)))

	// ak := s.providerApp.GetTestAccountKeeper()
	// ak.GetModuleAccount(ctx)
	// ak := s.providerApp.GetTestAccountKeeper().SetModuleAccount(s.providerCtx(), consuModAcct)

	// fees := sdk.NewCoins(sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(100)))
	// err := s.providerApp.GetTestBankKeeper().SendCoinsFromAccountToModule(s.providerCtx(), delAddr, moduleName, fees)

	// s.Require().NoError(err)

	// delegate(s, delAddr, bondAmt)
	// s.providerChain.NextBlock()

	// // register a consumer reward denom
	// params := s.consumerApp.GetConsumerKeeper().GetConsumerParams(s.consumerCtx())
	// params.RewardDenoms = []string{sdk.DefaultBondDenom}
	// s.consumerApp.GetConsumerKeeper().SetParams(s.consumerCtx(), params)

	// // relay VSC packets from provider to consumer
	// relayAllCommittedPackets(s, s.providerChain, s.path, ccv.ProviderPortID, s.path.EndpointB.ChannelID, 1)

	// // reward for the provider chain will be sent after each 2 blocks
	// consumerParams := s.consumerApp.GetSubspace(consumertypes.ModuleName)
	// consumerParams.Set(s.consumerCtx(), ccv.KeyBlocksPerDistributionTransmission, int64(2))
	// s.consumerChain.NextBlock()

	// consumerAccountKeeper := s.consumerApp.GetTestAccountKeeper()
	// providerAccountKeeper := s.providerApp.GetTestAccountKeeper()
	// consumerBankKeeper := s.consumerApp.GetTestBankKeeper()
	// providerBankKeeper := s.providerApp.GetTestBankKeeper()

	// // send coins to the fee pool which is used for reward distribution
	// consumerFeePoolAddr := consumerAccountKeeper.GetModuleAccount(s.consumerCtx(), authtypes.FeeCollectorName).GetAddress()
	// feePoolTokensOld := consumerBankKeeper.GetAllBalances(s.consumerCtx(), consumerFeePoolAddr)
	// fees := sdk.NewCoins(sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(100)))
	// err := consumerBankKeeper.SendCoinsFromAccountToModule(s.consumerCtx(), s.consumerChain.SenderAccount.GetAddress(), authtypes.FeeCollectorName, fees)
	// s.Require().NoError(err)
	// feePoolTokens := consumerBankKeeper.GetAllBalances(s.consumerCtx(), consumerFeePoolAddr)
	// s.Require().Equal(sdk.NewInt(100).Add(feePoolTokensOld.AmountOf(sdk.DefaultBondDenom)), feePoolTokens.AmountOf(sdk.DefaultBondDenom))

	// // calculate the reward for consumer and provider chain. Consumer will receive ConsumerRedistributeFrac, the rest is going to provider
	// frac, err := sdk.NewDecFromStr(s.consumerApp.GetConsumerKeeper().GetConsumerRedistributionFrac(s.consumerCtx()))
	// s.Require().NoError(err)
	// consumerExpectedRewards, _ := sdk.NewDecCoinsFromCoins(feePoolTokens...).MulDec(frac).TruncateDecimal()
	// providerExpectedRewards := feePoolTokens.Sub(consumerExpectedRewards...)
	// s.consumerChain.NextBlock()

	// // amount from the fee pool is divided between consumer redistribute address and address reserved for provider chain
	// feePoolTokens = consumerBankKeeper.GetAllBalances(s.consumerCtx(), consumerFeePoolAddr)
	// s.Require().Equal(0, len(feePoolTokens))
	// consumerRedistributeAddr := consumerAccountKeeper.GetModuleAccount(s.consumerCtx(), consumertypes.ConsumerRedistributeName).GetAddress()
	// consumerTokens := consumerBankKeeper.GetAllBalances(s.consumerCtx(), consumerRedistributeAddr)
	// s.Require().Equal(consumerExpectedRewards.AmountOf(sdk.DefaultBondDenom), consumerTokens.AmountOf(sdk.DefaultBondDenom))
	// providerRedistributeAddr := consumerAccountKeeper.GetModuleAccount(s.consumerCtx(), consumertypes.ConsumerToSendToProviderName).GetAddress()
	// providerTokens := consumerBankKeeper.GetAllBalances(s.consumerCtx(), providerRedistributeAddr)
	// s.Require().Equal(providerExpectedRewards.AmountOf(sdk.DefaultBondDenom), providerTokens.AmountOf(sdk.DefaultBondDenom))

	// // send the reward to provider chain after 2 blocks

	// s.consumerChain.NextBlock()
	// providerTokens = consumerBankKeeper.GetAllBalances(s.consumerCtx(), providerRedistributeAddr)
	// s.Require().Equal(0, len(providerTokens))

	// relayAllCommittedPackets(s, s.consumerChain, s.transferPath, transfertypes.PortID, s.transferPath.EndpointA.ChannelID, 1)
	// s.providerChain.NextBlock()

	// // Since consumer reward denom is not yet registered, the coins never get into the fee pool, staying in the ConsumerRewardsPool
	// rewardPool := providerAccountKeeper.GetModuleAccount(s.providerCtx(), providertypes.ConsumerRewardsPool).GetAddress()
	// rewardCoins := providerBankKeeper.GetAllBalances(s.providerCtx(), rewardPool)

	// ibcCoinIndex := -1
	// for i, coin := range rewardCoins {
	// 	if strings.HasPrefix(coin.Denom, "ibc") {
	// 		ibcCoinIndex = i
	// 	}
	// }

	// // Check that we found an ibc denom in the reward pool
	// s.Require().Greater(ibcCoinIndex, -1)

	// // Check that the coins got into the ConsumerRewardsPool
	// s.Require().True(rewardCoins[ibcCoinIndex].Amount.Equal(providerExpectedRewards[0].Amount))

	// // Advance a block and check that the coins are still in the ConsumerRewardsPool
	// s.providerChain.NextBlock()
	// rewardCoins = providerBankKeeper.GetAllBalances(s.providerCtx(), rewardPool)
	// s.Require().True(rewardCoins[ibcCoinIndex].Amount.Equal(providerExpectedRewards[0].Amount))

	// // Set the consumer reward denom. This would be done by a governance proposal in prod
	// s.providerApp.GetProviderKeeper().SetConsumerRewardDenom(s.providerCtx(), rewardCoins[ibcCoinIndex].Denom)

	// s.providerChain.NextBlock()

	// // Check that the reward pool has no more coins because they were transferred to the fee pool
	// rewardCoins = providerBankKeeper.GetAllBalances(s.providerCtx(), rewardPool)
	// s.Require().Equal(0, len(rewardCoins))

	// // check that the fee pool has the expected amount of coins
	// communityCoins := s.providerApp.GetTestDistributionKeeper().GetFeePoolCommunityCoins(s.providerCtx())
	// s.Require().True(communityCoins[ibcCoinIndex].Amount.Equal(sdk.NewDecCoinFromCoin(providerExpectedRewards[0]).Amount))
}
