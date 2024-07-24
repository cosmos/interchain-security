package integration

import (
	"strings"

	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"

	"cosmossdk.io/math"
	distrtypes "github.com/cosmos/cosmos-sdk/x/distribution/types"
	transfertypes "github.com/cosmos/ibc-go/v8/modules/apps/transfer/types"
	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v8/modules/core/04-channel/types"

	sdk "github.com/cosmos/cosmos-sdk/types"
	icstestingutils "github.com/cosmos/interchain-security/v5/testutil/integration"
	consumerkeeper "github.com/cosmos/interchain-security/v5/x/ccv/consumer/keeper"
	consumertypes "github.com/cosmos/interchain-security/v5/x/ccv/consumer/types"
	providerkeeper "github.com/cosmos/interchain-security/v5/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/v5/x/ccv/types"
)

// This test is valid for minimal viable consumer chain
func (s *CCVTestSuite) TestRewardsDistribution() {
	// set up channel and delegate some tokens in order for validator set update to be sent to the consumer chain
	s.SetupCCVChannel(s.path)
	s.SetupTransferChannel()
	bondAmt := math.NewInt(10000000)
	delAddr := s.providerChain.SenderAccount.GetAddress()
	delegate(s, delAddr, bondAmt)
	s.nextEpoch()

	// register a consumer reward denom
	params := s.consumerApp.GetConsumerKeeper().GetConsumerParams(s.consumerCtx())
	params.RewardDenoms = []string{sdk.DefaultBondDenom}
	s.consumerApp.GetConsumerKeeper().SetParams(s.consumerCtx(), params)

	// relay VSC packets from provider to consumer
	relayAllCommittedPackets(s, s.providerChain, s.path, ccv.ProviderPortID, s.path.EndpointB.ChannelID, 1)

	// reward for the provider chain will be sent after each 2 blocks
	s.consumerApp.GetConsumerKeeper().SetBlocksPerDistributionTransmission(s.consumerCtx(), 2)
	s.consumerChain.NextBlock()

	consumerAccountKeeper := s.consumerApp.GetTestAccountKeeper()
	providerAccountKeeper := s.providerApp.GetTestAccountKeeper()
	consumerBankKeeper := s.consumerApp.GetTestBankKeeper()
	providerBankKeeper := s.providerApp.GetTestBankKeeper()
	providerKeeper := s.providerApp.GetProviderKeeper()
	providerDistributionKeeper := s.providerApp.GetTestDistributionKeeper()

	// send coins to the fee pool which is used for reward distribution
	consumerFeePoolAddr := consumerAccountKeeper.GetModuleAccount(s.consumerCtx(), authtypes.FeeCollectorName).GetAddress()
	feePoolTokensOld := consumerBankKeeper.GetAllBalances(s.consumerCtx(), consumerFeePoolAddr)
	fees := sdk.NewCoins(sdk.NewCoin(sdk.DefaultBondDenom, math.NewInt(100)))
	err := consumerBankKeeper.SendCoinsFromAccountToModule(s.consumerCtx(), s.consumerChain.SenderAccount.GetAddress(), authtypes.FeeCollectorName, fees)
	s.Require().NoError(err)

	feePoolTokens := consumerBankKeeper.GetAllBalances(s.consumerCtx(), consumerFeePoolAddr)
	s.Require().Equal(math.NewInt(100).Add(feePoolTokensOld.AmountOf(sdk.DefaultBondDenom)), feePoolTokens.AmountOf(sdk.DefaultBondDenom))

	// calculate the reward for consumer and provider chain. Consumer will receive ConsumerRedistributeFrac, the rest is going to provider
	frac, err := math.LegacyNewDecFromStr(s.consumerApp.GetConsumerKeeper().GetConsumerRedistributionFrac(s.consumerCtx()))
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
	rewardPool := providerAccountKeeper.GetModuleAccount(s.providerCtx(), providertypes.ConsumerRewardsPool).GetAddress()
	rewardCoins := providerBankKeeper.GetAllBalances(s.providerCtx(), rewardPool)

	// Check that the reward pool contains a coin with an IBC denom
	rewardsIBCdenom := ""
	for _, coin := range rewardCoins {
		if strings.HasPrefix(coin.Denom, "ibc") {
			rewardsIBCdenom = coin.Denom
		}
	}
	s.Require().NotZero(rewardsIBCdenom)

	// Check that the coins got into the ConsumerRewardsPool
	providerExpRewardsAmount := providerExpectedRewards.AmountOf(sdk.DefaultBondDenom)
	s.Require().Equal(rewardCoins.AmountOf(rewardsIBCdenom), providerExpRewardsAmount)

	// Advance a block and check that the coins are still in the ConsumerRewardsPool
	s.providerChain.NextBlock()
	rewardCoins = providerBankKeeper.GetAllBalances(s.providerCtx(), rewardPool)
	s.Require().Equal(rewardCoins.AmountOf(rewardsIBCdenom), providerExpRewardsAmount)

	// Set the consumer reward denom. This would be done by a governance proposal in prod.
	providerKeeper.SetConsumerRewardDenom(s.providerCtx(), rewardsIBCdenom)

	// Refill the consumer fee pool
	err = consumerBankKeeper.SendCoinsFromAccountToModule(
		s.consumerCtx(),
		s.consumerChain.SenderAccount.GetAddress(),
		authtypes.FeeCollectorName,
		fees,
	)
	s.Require().NoError(err)

	// Pass two blocks
	s.consumerChain.NextBlock()
	s.consumerChain.NextBlock()

	// Save the consumer validators total outstanding rewards on the provider
	consumerValsOutstandingRewardsFunc := func(ctx sdk.Context) sdk.DecCoins {
		totalRewards := sdk.DecCoins{}
		vals, err := providerKeeper.GetConsumerValSet(ctx, s.consumerChain.ChainID)
		s.Require().NoError(err)

		for _, v := range vals {
			val, err := s.providerApp.GetTestStakingKeeper().GetValidatorByConsAddr(ctx, sdk.ConsAddress(v.ProviderConsAddr))
			s.Require().NoError(err)
			valAddr, err := sdk.ValAddressFromBech32(val.GetOperator())
			s.Require().NoError(err)
			valReward, _ := providerDistributionKeeper.GetValidatorOutstandingRewards(ctx, valAddr)
			totalRewards = totalRewards.Add(valReward.Rewards...)
		}
		return totalRewards
	}
	consuValsRewards := consumerValsOutstandingRewardsFunc(s.providerCtx())

	// increase the block height so validators are eligible for consumer rewards (see `IsEligibleForConsumerRewards`)
	numberOfBlocksToStartReceivingRewards := providerKeeper.GetNumberOfEpochsToStartReceivingRewards(s.providerCtx()) * providerKeeper.GetBlocksPerEpoch(s.providerCtx())

	for s.providerCtx().BlockHeight() <= numberOfBlocksToStartReceivingRewards {
		s.providerChain.NextBlock()
	}

	// Transfer rewards from consumer to provider and distribute rewards to
	// validators and community pool by calling BeginBlockRD
	relayAllCommittedPackets(
		s,
		s.consumerChain,
		s.transferPath,
		transfertypes.PortID,
		s.transferPath.EndpointA.ChannelID,
		1,
	)

	// Consumer allocations are distributed between the validators and the community pool.
	// The decimals resulting from the distribution are expected to remain in the consumer allocations.
	rewardsAlloc := providerKeeper.GetConsumerRewardsAllocation(s.providerCtx(), s.consumerChain.ChainID)
	remainingAlloc := rewardsAlloc.Rewards.AmountOf(rewardsIBCdenom)
	s.Require().True(remainingAlloc.LTE(math.LegacyOneDec()))

	// Check that the reward pool still holds the coins from the first transfer
	// which were never allocated since they were not whitelisted
	// plus the remaining decimals from the second transfer.
	rewardCoins = providerBankKeeper.GetAllBalances(s.providerCtx(), rewardPool)
	s.Require().Equal(
		math.LegacyNewDecFromInt(rewardCoins.AmountOf(rewardsIBCdenom)),
		math.LegacyNewDecFromInt(providerExpRewardsAmount).Add(remainingAlloc),
	)

	// Check that the distribution module account balance is equal to the consumer rewards
	consuValsRewardsReceived := consumerValsOutstandingRewardsFunc(s.providerCtx()).Sub(consuValsRewards)
	distrAcct := providerDistributionKeeper.GetDistributionAccount(s.providerCtx())
	distrAcctBalance := providerBankKeeper.GetAllBalances(s.providerCtx(), distrAcct.GetAddress())

	s.Require().Equal(
		// ceil the total consumer rewards since the validators allocation use some rounding
		consuValsRewardsReceived.AmountOf(rewardsIBCdenom).Ceil(),
		math.LegacyNewDecFromInt(distrAcctBalance.AmountOf(rewardsIBCdenom)),
	)
}

// TestSendRewardsRetries tests that failed reward transmissions are retried every BlocksPerDistributionTransmission blocks
func (s *CCVTestSuite) TestSendRewardsRetries() {
	// TODO: this setup can be consolidated with other tests in the file

	// ccv and transmission channels setup
	s.SetupCCVChannel(s.path)
	s.SetupTransferChannel()
	bondAmt := math.NewInt(10000000)
	delAddr := s.providerChain.SenderAccount.GetAddress()
	delegate(s, delAddr, bondAmt)
	s.nextEpoch()

	// Register denom on consumer chain
	params := s.consumerApp.GetConsumerKeeper().GetConsumerParams(s.consumerCtx())
	params.RewardDenoms = []string{sdk.DefaultBondDenom}
	s.consumerApp.GetConsumerKeeper().SetParams(s.consumerCtx(), params)

	// relay VSC packets from provider to consumer
	relayAllCommittedPackets(s, s.providerChain, s.path, ccv.ProviderPortID, s.path.EndpointB.ChannelID, 1)

	consumerBankKeeper := s.consumerApp.GetTestBankKeeper()
	consumerKeeper := s.consumerApp.GetConsumerKeeper()

	// reward for the provider chain will be sent after each 1000 blocks
	s.consumerApp.GetConsumerKeeper().SetBlocksPerDistributionTransmission(s.consumerCtx(), 1000)

	// fill fee pool
	fees := sdk.NewCoins(sdk.NewCoin(sdk.DefaultBondDenom, math.NewInt(100)))
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
		bondAmt := math.NewInt(10000000)
		delAddr := s.providerChain.SenderAccount.GetAddress()
		delegate(s, delAddr, bondAmt)
		s.nextEpoch()

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
		s.consumerApp.GetConsumerKeeper().SetBlocksPerDistributionTransmission(s.consumerCtx(), 1000)

		// fill fee pool
		fees := sdk.NewCoins(sdk.NewCoin(sdk.DefaultBondDenom, math.NewInt(100)))
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
					sdk.NewCoins(sdk.NewCoin(sdk.DefaultBondDenom, math.NewInt(100))),
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
					sdk.NewCoins(sdk.NewCoin(sdk.DefaultBondDenom, math.NewInt(100))),
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
					sdk.NewCoins(sdk.NewCoin(sdk.DefaultBondDenom, math.NewInt(100))),
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
		bondAmt := math.NewInt(10000000)
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

// TestIBCTransferMiddleware tests the logic of the IBC transfer OnRecvPacket callback
func (s *CCVTestSuite) TestIBCTransferMiddleware() {
	var (
		data        transfertypes.FungibleTokenPacketData
		packet      channeltypes.Packet
		getIBCDenom func(string, string) string
	)

	testCases := []struct {
		name             string
		setup            func(sdk.Context, *providerkeeper.Keeper, icstestingutils.TestBankKeeper)
		rewardsAllocated bool
		expErr           bool
	}{
		{
			"invalid IBC packet",
			func(sdk.Context, *providerkeeper.Keeper, icstestingutils.TestBankKeeper) {
				packet = channeltypes.Packet{}
			},
			false,
			true,
		},
		{
			"IBC packet sender isn't a consumer chain",
			func(ctx sdk.Context, keeper *providerkeeper.Keeper, bankKeeper icstestingutils.TestBankKeeper) {
				// make the sender consumer chain impossible to identify
				packet.DestinationChannel = "CorruptedChannelId"
			},
			false,
			false,
		},
		{
			"IBC Transfer recipient is not the consumer rewards pool address",
			func(ctx sdk.Context, keeper *providerkeeper.Keeper, bankKeeper icstestingutils.TestBankKeeper) {
				data.Receiver = "cosmos149lw9fktlqfed3zt8ah48r5czmsug5s7kw77u9" // random acct address
				packet.Data = data.GetBytes()
			},
			false,
			false,
		},
		{
			"IBC Transfer coin denom isn't registered",
			func(ctx sdk.Context, keeper *providerkeeper.Keeper, bankKeeper icstestingutils.TestBankKeeper) {},
			false,
			false,
		},
		{
			"successful token transfer to empty pool",
			func(ctx sdk.Context, keeper *providerkeeper.Keeper, bankKeeper icstestingutils.TestBankKeeper) {
				keeper.SetConsumerRewardDenom(
					s.providerCtx(),
					getIBCDenom(packet.DestinationPort, packet.DestinationChannel),
				)
			},
			true,
			false,
		},
		{
			"successful token transfer to filled pool",
			func(ctx sdk.Context, keeper *providerkeeper.Keeper, bankKeeper icstestingutils.TestBankKeeper) {
				keeper.SetConsumerRewardDenom(
					ctx,
					getIBCDenom(packet.DestinationPort, packet.DestinationChannel),
				)

				// fill consumer reward pool
				bankKeeper.SendCoinsFromAccountToModule(
					ctx,
					s.providerChain.SenderAccount.GetAddress(),
					providertypes.ConsumerRewardsPool,
					sdk.NewCoins(sdk.NewCoin(sdk.DefaultBondDenom, math.NewInt(100_000))),
				)
				// update consumer allocation
				keeper.SetConsumerRewardsAllocation(
					ctx,
					s.consumerChain.ChainID,
					providertypes.ConsumerRewardsAllocation{
						Rewards: sdk.NewDecCoins(sdk.NewDecCoin(sdk.DefaultBondDenom, math.NewInt(100_000))),
					},
				)
			},
			true,
			false,
		},
	}

	for _, tc := range testCases {
		s.Run(tc.name, func() {
			s.SetupTest()
			s.SetupCCVChannel(s.path)
			s.SetupTransferChannel()

			providerKeeper := s.providerApp.GetProviderKeeper()
			bankKeeper := s.providerApp.GetTestBankKeeper()
			amount := math.NewInt(100)

			data = transfertypes.NewFungibleTokenPacketData( // can be explicitly changed in setup
				sdk.DefaultBondDenom,
				amount.String(),
				authtypes.NewModuleAddress(consumertypes.ConsumerToSendToProviderName).String(),
				providerKeeper.GetConsumerRewardsPoolAddressStr(s.providerCtx()),
				"",
			)

			packet = channeltypes.NewPacket( // can be explicitly changed in setup
				data.GetBytes(),
				uint64(1),
				s.transferPath.EndpointA.ChannelConfig.PortID,
				s.transferPath.EndpointA.ChannelID,
				s.transferPath.EndpointB.ChannelConfig.PortID,
				s.transferPath.EndpointB.ChannelID,
				clienttypes.NewHeight(1, 100),
				0,
			)

			providerKeeper.SetConsumerRewardDenom(s.providerCtx(),
				transfertypes.GetPrefixedDenom(
					packet.DestinationPort,
					packet.DestinationChannel,
					sdk.DefaultBondDenom,
				),
			)

			getIBCDenom = func(dstPort, dstChannel string) string {
				return transfertypes.ParseDenomTrace(
					transfertypes.GetPrefixedDenom(
						packet.DestinationPort,
						packet.DestinationChannel,
						sdk.DefaultBondDenom,
					),
				).IBCDenom()
			}

			tc.setup(s.providerCtx(), &providerKeeper, bankKeeper)

			cbs, ok := s.providerChain.App.GetIBCKeeper().Router.GetRoute(transfertypes.ModuleName)
			s.Require().True(ok)

			// save the IBC transfer rewards transferred
			rewardsPoolBalance := bankKeeper.GetAllBalances(s.providerCtx(), sdk.MustAccAddressFromBech32(data.Receiver))

			// save the consumer's rewards allocated
			consumerRewardsAllocations := providerKeeper.GetConsumerRewardsAllocation(s.providerCtx(), s.consumerChain.ChainID)

			// execute middleware OnRecvPacket logic
			ack := cbs.OnRecvPacket(s.providerCtx(), packet, sdk.AccAddress{})

			// compute expected rewards with provider denom
			expRewards := sdk.Coin{
				Amount: amount,
				Denom:  getIBCDenom(packet.DestinationPort, packet.DestinationChannel),
			}

			// compute the balance and allocation difference
			rewardsTransferred := bankKeeper.GetAllBalances(s.providerCtx(), sdk.MustAccAddressFromBech32(data.Receiver)).
				Sub(rewardsPoolBalance...)
			rewardsAllocated := providerKeeper.GetConsumerRewardsAllocation(s.providerCtx(), s.consumerChain.ChainID).
				Rewards.Sub(consumerRewardsAllocations.Rewards)

			if !tc.expErr {
				s.Require().True(ack.Success())
				// verify that the consumer rewards pool received the IBC coins
				s.Require().Equal(rewardsTransferred, sdk.Coins{expRewards})

				if tc.rewardsAllocated {
					// check the data receiver address is set to the consumer rewards pool address
					s.Require().Equal(data.GetReceiver(), providerKeeper.GetConsumerRewardsPoolAddressStr(s.providerCtx()))

					// verify that consumer rewards allocation is updated
					s.Require().Equal(rewardsAllocated, sdk.NewDecCoinsFromCoins(expRewards))
				} else {
					// verify that consumer rewards aren't allocated
					s.Require().Empty(rewardsAllocated)
				}
			} else {
				s.Require().False(ack.Success())
			}
		})
	}
}

// TestAllocateTokens is a happy-path test of the consumer rewards pool allocation
// to opted-in validators and the community pool
func (s *CCVTestSuite) TestAllocateTokens() {
	// set up channel and delegate some tokens in order for validator set update to be sent to the consumer chain
	s.SetupAllCCVChannels()
	providerKeeper := s.providerApp.GetProviderKeeper()
	bankKeeper := s.providerApp.GetTestBankKeeper()
	distributionKeeper := s.providerApp.GetTestDistributionKeeper()
	accountKeeper := s.providerApp.GetTestAccountKeeper()

	getDistrAcctBalFn := func(ctx sdk.Context) sdk.DecCoins {
		bal := bankKeeper.GetAllBalances(ctx, accountKeeper.GetModuleAccount(ctx, distrtypes.ModuleName).GetAddress())
		return sdk.NewDecCoinsFromCoins(bal...)
	}

	totalRewards := sdk.Coins{sdk.NewCoin(sdk.DefaultBondDenom, math.NewInt(100))}

	// increase the block height so validators are eligible for consumer rewards (see `IsEligibleForConsumerRewards`)
	numberOfBlocksToStartReceivingRewards := providerKeeper.GetNumberOfEpochsToStartReceivingRewards(
		s.providerCtx()) * providerKeeper.GetBlocksPerEpoch(s.providerCtx())
	providerCtx := s.providerCtx().WithBlockHeight(numberOfBlocksToStartReceivingRewards + s.providerCtx().BlockHeight())

	// fund consumer rewards pool
	bankKeeper.SendCoinsFromAccountToModule(
		providerCtx,
		s.providerChain.SenderAccount.GetAddress(),
		providertypes.ConsumerRewardsPool,
		totalRewards,
	)

	// Allocate rewards evenly between consumers
	rewardsPerChain := totalRewards.QuoInt(math.NewInt(int64(len(s.consumerBundles))))
	for chainID := range s.consumerBundles {
		// update consumer allocation
		providerKeeper.SetConsumerRewardsAllocation(
			providerCtx,
			chainID,
			providertypes.ConsumerRewardsAllocation{
				Rewards: sdk.NewDecCoinsFromCoins(rewardsPerChain...),
			},
		)
	}

	// iterate over the validators and verify that no validator has outstanding rewards
	totalValsRewards := sdk.DecCoins{}
	for _, val := range s.providerChain.Vals.Validators {
		valRewards, err := distributionKeeper.GetValidatorOutstandingRewards(providerCtx, sdk.ValAddress(val.Address))
		s.Require().NoError(err)
		totalValsRewards = totalValsRewards.Add(valRewards.Rewards...)
	}

	s.Require().True(totalValsRewards.IsZero())

	// At this point the distribution module account
	// only holds the community pool's tokens
	// since there are no validators with outstanding rewards
	lastCommPool := getDistrAcctBalFn(providerCtx)

	// execute BeginBlock to trigger the token allocation
	providerKeeper.BeginBlockRD(providerCtx)

	valNum := len(s.providerChain.Vals.Validators)
	consNum := len(s.consumerBundles)

	// compute the expected validators token allocation by subtracting the community tax
	rewardsPerChainDec := sdk.NewDecCoinsFromCoins(rewardsPerChain...)
	communityTax, err := distributionKeeper.GetCommunityTax(providerCtx)
	s.Require().NoError(err)

	rewardsPerChainTrunc, _ := rewardsPerChainDec.
		MulDecTruncate(math.LegacyOneDec().Sub(communityTax)).TruncateDecimal()
	validatorsExpRewardsPerChain := sdk.NewDecCoinsFromCoins(rewardsPerChainTrunc...).QuoDec(math.LegacyNewDec(int64(valNum)))
	// multiply by the number of consumers
	validatorsExpRewards := validatorsExpRewardsPerChain.MulDec(math.LegacyNewDec(int64(consNum)))

	// verify the validator tokens allocation
	// note that the validators have the same voting power to keep things simple
	for _, val := range s.providerChain.Vals.Validators {
		valRewards, err := distributionKeeper.GetValidatorOutstandingRewards(providerCtx, sdk.ValAddress(val.Address))
		s.Require().NoError(err)

		s.Require().Equal(
			valRewards.Rewards,
			validatorsExpRewards,
		)
	}

	// check that the total expected rewards are transferred to the distribution module account

	// store the decimal remainders in the consumer reward allocations
	allocRemainderPerChain := providerKeeper.GetConsumerRewardsAllocation(providerCtx, s.consumerChain.ChainID).Rewards

	// compute the total rewards distributed to the distribution module balance (validator outstanding rewards + community pool tax),
	totalRewardsDistributed := sdk.NewDecCoinsFromCoins(totalRewards...).Sub(allocRemainderPerChain.MulDec(math.LegacyNewDec(int64(consNum))))

	// compare the expected total rewards against the distribution module balance
	s.Require().Equal(lastCommPool.Add(totalRewardsDistributed...), getDistrAcctBalFn(providerCtx))
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

func (s *CCVTestSuite) TestAllocateTokensToConsumerValidators() {
	providerKeeper := s.providerApp.GetProviderKeeper()
	distributionKeeper := s.providerApp.GetTestDistributionKeeper()
	bankKeeper := s.providerApp.GetTestBankKeeper()

	chainID := s.consumerChain.ChainID

	testCases := []struct {
		name         string
		consuValLen  int
		tokens       sdk.DecCoins
		rate         math.LegacyDec
		expAllocated sdk.DecCoins
	}{
		{
			name:         "tokens are empty",
			tokens:       sdk.DecCoins{},
			rate:         math.LegacyZeroDec(),
			expAllocated: nil,
		},
		{
			name:         "consumer valset is empty - total voting power is zero",
			tokens:       sdk.DecCoins{sdk.NewDecCoin(sdk.DefaultBondDenom, math.NewInt(100_000))},
			rate:         math.LegacyZeroDec(),
			expAllocated: nil,
		},
		{
			name:         "expect all tokens to be allocated to a single validator",
			consuValLen:  1,
			tokens:       sdk.DecCoins{sdk.NewDecCoin(sdk.DefaultBondDenom, math.NewInt(999))},
			rate:         math.LegacyNewDecWithPrec(5, 1),
			expAllocated: sdk.DecCoins{sdk.NewDecCoin(sdk.DefaultBondDenom, math.NewInt(999))},
		},
		{
			name:         "expect tokens to be allocated evenly between validators",
			consuValLen:  2,
			tokens:       sdk.DecCoins{sdk.NewDecCoinFromDec(sdk.DefaultBondDenom, math.LegacyNewDecFromIntWithPrec(math.NewInt(999), 2))},
			rate:         math.LegacyOneDec(),
			expAllocated: sdk.DecCoins{sdk.NewDecCoinFromDec(sdk.DefaultBondDenom, math.LegacyNewDecFromIntWithPrec(math.NewInt(999), 2))},
		},
	}

	for _, tc := range testCases {
		s.Run(tc.name, func() {
			ctx, _ := s.providerCtx().CacheContext()

			// increase the block height so validators are eligible for consumer rewards (see `IsEligibleForConsumerRewards`)
			ctx = ctx.WithBlockHeight(providerKeeper.GetNumberOfEpochsToStartReceivingRewards(ctx)*providerKeeper.GetBlocksPerEpoch(ctx) +
				ctx.BlockHeight())

			// change the consumer valset
			consuVals, err := providerKeeper.GetConsumerValSet(ctx, chainID)
			s.Require().NoError(err)
			providerKeeper.DeleteConsumerValSet(ctx, chainID)
			providerKeeper.SetConsumerValSet(ctx, chainID, consuVals[0:tc.consuValLen])
			consuVals, err = providerKeeper.GetConsumerValSet(ctx, chainID)
			s.Require().NoError(err)

			// set the same consumer commission rate for all consumer validators
			for _, v := range consuVals {
				provAddr := providertypes.NewProviderConsAddress(sdk.ConsAddress(v.ProviderConsAddr))
				err := providerKeeper.SetConsumerCommissionRate(
					ctx,
					chainID,
					provAddr,
					tc.rate,
				)
				s.Require().NoError(err)
			}

			// allocate tokens
			res := providerKeeper.AllocateTokensToConsumerValidators(
				ctx,
				chainID,
				tc.tokens,
			)

			// check that the expected result is returned
			s.Require().Equal(tc.expAllocated, res)

			if !tc.expAllocated.Empty() {
				// rewards are expected to be allocated evenly between validators
				rewardsPerVal := tc.expAllocated.QuoDec(math.LegacyNewDec(int64(len(consuVals))))

				// check that the rewards are allocated to validators
				for _, v := range consuVals {
					valAddr := sdk.ValAddress(v.ProviderConsAddr)
					rewards, err := s.providerApp.GetTestDistributionKeeper().GetValidatorOutstandingRewards(
						ctx,
						valAddr,
					)
					s.Require().NoError(err)
					s.Require().Equal(rewardsPerVal, rewards.Rewards)

					// send rewards to the distribution module
					valRewardsTrunc, _ := rewards.Rewards.TruncateDecimal()
					err = bankKeeper.SendCoinsFromAccountToModule(
						ctx,
						s.providerChain.SenderAccount.GetAddress(),
						distrtypes.ModuleName,
						valRewardsTrunc)
					s.Require().NoError(err)

					// check that validators can withdraw their rewards
					withdrawnCoins, err := distributionKeeper.WithdrawValidatorCommission(
						ctx,
						valAddr,
					)
					s.Require().NoError(err)

					// check that the withdrawn coins is equal to the entire reward amount
					// times the set consumer commission rate
					commission := rewards.Rewards.MulDec(tc.rate)
					c, _ := commission.TruncateDecimal()
					s.Require().Equal(withdrawnCoins, c)

					// check that validators get rewards in their balance
					s.Require().Equal(withdrawnCoins, bankKeeper.GetAllBalances(ctx, sdk.AccAddress(valAddr)))
				}
			} else {
				for _, v := range consuVals {
					valAddr := sdk.ValAddress(v.ProviderConsAddr)
					rewards, err := s.providerApp.GetTestDistributionKeeper().GetValidatorOutstandingRewards(
						ctx,
						valAddr,
					)
					s.Require().NoError(err)
					s.Require().Zero(rewards.Rewards)
				}
			}
		})
	}
}

// TestAllocateTokensToConsumerValidatorsWithDifferentValidatorHeights tests `AllocateTokensToConsumerValidators` with
// consumer validators that have different heights. Specifically, test that validators that have been consumer validators
// for some time receive rewards, while validators that recently became consumer validators do not receive rewards.
func (s *CCVTestSuite) TestAllocateTokensToConsumerValidatorsWithDifferentValidatorHeights() {
	// Note this test is an adaptation of a `TestAllocateTokensToConsumerValidators` testcase.
	providerKeeper := s.providerApp.GetProviderKeeper()
	distributionKeeper := s.providerApp.GetTestDistributionKeeper()
	bankKeeper := s.providerApp.GetTestBankKeeper()

	chainID := s.consumerChain.ChainID

	tokens := sdk.DecCoins{sdk.NewDecCoinFromDec(sdk.DefaultBondDenom, math.LegacyNewDecFromIntWithPrec(math.NewInt(999), 2))}
	rate := math.LegacyOneDec()
	expAllocated := sdk.DecCoins{sdk.NewDecCoinFromDec(sdk.DefaultBondDenom, math.LegacyNewDecFromIntWithPrec(math.NewInt(999), 2))}

	ctx, _ := s.providerCtx().CacheContext()
	// If the provider chain has not yet reached `GetNumberOfEpochsToStartReceivingRewards * GetBlocksPerEpoch` block height,
	// then all validators receive rewards (see `IsEligibleForConsumerRewards`). In this test, we want to check whether
	// validators receive rewards or not based on how long they have been consumer validators. Because of this, we increase the block height.
	ctx = ctx.WithBlockHeight(providerKeeper.GetNumberOfEpochsToStartReceivingRewards(ctx)*providerKeeper.GetBlocksPerEpoch(ctx) + 1)

	// update the consumer validators
	consuVals, err := providerKeeper.GetConsumerValSet(ctx, chainID)
	s.Require().NoError(err)
	// first 2 validators were consumer validators since block height 1 and hence get rewards
	consuVals[0].JoinHeight = 1
	consuVals[1].JoinHeight = 1
	// last 2 validators were consumer validators since block height 2 and hence do not get rewards because they
	// have not been consumer validators for `GetNumberOfEpochsToStartReceivingRewards * GetBlocksPerEpoch` blocks
	consuVals[2].JoinHeight = 2
	consuVals[3].JoinHeight = 2
	providerKeeper.SetConsumerValSet(ctx, chainID, consuVals)

	providerKeeper.DeleteConsumerValSet(ctx, chainID)
	providerKeeper.SetConsumerValSet(ctx, chainID, consuVals)
	consuVals, err = providerKeeper.GetConsumerValSet(ctx, chainID)
	s.Require().NoError(err)

	// set the same consumer commission rate for all consumer validators
	for _, v := range consuVals {
		provAddr := providertypes.NewProviderConsAddress(sdk.ConsAddress(v.ProviderConsAddr))
		err := providerKeeper.SetConsumerCommissionRate(
			ctx,
			chainID,
			provAddr,
			rate,
		)
		s.Require().NoError(err)
	}

	// allocate tokens
	res := providerKeeper.AllocateTokensToConsumerValidators(
		ctx,
		chainID,
		tokens,
	)

	// check that the expected result is returned
	s.Require().Equal(expAllocated, res)

	// rewards are expected to be allocated evenly between validators 3 and 4
	rewardsPerVal := expAllocated.QuoDec(math.LegacyNewDec(int64(2)))

	// assert that the rewards are allocated to the first 2 validators
	for _, v := range consuVals[0:2] {
		valAddr := sdk.ValAddress(v.ProviderConsAddr)
		rewards, err := s.providerApp.GetTestDistributionKeeper().GetValidatorOutstandingRewards(
			ctx,
			valAddr,
		)
		s.Require().NoError(err)
		s.Require().Equal(rewardsPerVal, rewards.Rewards)

		// send rewards to the distribution module
		valRewardsTrunc, _ := rewards.Rewards.TruncateDecimal()
		err = bankKeeper.SendCoinsFromAccountToModule(
			ctx,
			s.providerChain.SenderAccount.GetAddress(),
			distrtypes.ModuleName,
			valRewardsTrunc)
		s.Require().NoError(err)

		// check that validators can withdraw their rewards
		withdrawnCoins, err := distributionKeeper.WithdrawValidatorCommission(
			ctx,
			valAddr,
		)
		s.Require().NoError(err)

		// check that the withdrawn coins is equal to the entire reward amount
		// times the set consumer commission rate
		commission := rewards.Rewards.MulDec(rate)
		c, _ := commission.TruncateDecimal()
		s.Require().Equal(withdrawnCoins, c)

		// check that validators get rewards in their balance
		s.Require().Equal(withdrawnCoins, bankKeeper.GetAllBalances(ctx, sdk.AccAddress(valAddr)))
	}

	// assert that no rewards are allocated to the last 2 validators because they have not been consumer validators
	// for at least `GetNumberOfEpochsToStartReceivingRewards * GetBlocksPerEpoch` blocks
	for _, v := range consuVals[2:4] {
		valAddr := sdk.ValAddress(v.ProviderConsAddr)
		rewards, err := s.providerApp.GetTestDistributionKeeper().GetValidatorOutstandingRewards(
			ctx,
			valAddr,
		)
		s.Require().NoError(err)
		s.Require().Zero(rewards.Rewards)
	}
}

// TestMultiConsumerRewardsDistribution tests the rewards distribution of multiple consumers chains
func (s *CCVTestSuite) TestMultiConsumerRewardsDistribution() {
	s.SetupAllCCVChannels()
	s.SetupAllTransferChannels()

	providerBankKeeper := s.providerApp.GetTestBankKeeper()
	providerAccountKeeper := s.providerApp.GetTestAccountKeeper()

	// check that the reward provider pool is empty
	rewardPool := providerAccountKeeper.GetModuleAccount(s.providerCtx(), providertypes.ConsumerRewardsPool).GetAddress()
	rewardCoins := providerBankKeeper.GetAllBalances(s.providerCtx(), rewardPool)
	s.Require().Empty(rewardCoins)

	// totalConsumerRewards := sdk.Coins{}

	// Iterate over the consumers and perform the reward distribution
	// to the provider
	for chainID := range s.consumerBundles {
		bundle := s.consumerBundles[chainID]
		consumerKeeper := bundle.App.GetConsumerKeeper()
		bankKeeper := bundle.App.GetTestBankKeeper()
		accountKeeper := bundle.App.GetTestAccountKeeper()

		// set the consumer reward denom and the block per distribution params
		params := consumerKeeper.GetConsumerParams(bundle.GetCtx())
		params.RewardDenoms = []string{sdk.DefaultBondDenom}
		// set the reward distribution to be performed during the next block
		params.BlocksPerDistributionTransmission = int64(1)
		consumerKeeper.SetParams(bundle.GetCtx(), params)

		// transfer the consumer reward pool to the provider
		var rewardsPerConsumer sdk.Coin

		// check the consumer pool balance
		// Note that for a democracy consumer chain the pool may already be filled
		pool := bankKeeper.GetAllBalances(
			bundle.GetCtx(),
			accountKeeper.GetModuleAccount(bundle.GetCtx(), consumertypes.ConsumerToSendToProviderName).GetAddress(),
		)
		if pool.Empty() {
			// if pool is empty, fill it with some tokens
			rewardsPerConsumer = sdk.NewCoin(sdk.DefaultBondDenom, math.NewInt(100))
			err := bankKeeper.SendCoinsFromAccountToModule(
				bundle.GetCtx(),
				bundle.Chain.SenderAccount.GetAddress(),
				consumertypes.ConsumerToSendToProviderName,
				sdk.NewCoins(rewardsPerConsumer),
			)
			s.Require().NoError(err)
		}

		// perform the reward transfer
		bundle.Chain.NextBlock()

		// construct the denom of the reward tokens for the provider
		prefixedDenom := transfertypes.GetPrefixedDenom(
			transfertypes.PortID,
			bundle.TransferPath.EndpointB.ChannelID,
			rewardsPerConsumer.Denom,
		)
		provIBCDenom := transfertypes.ParseDenomTrace(prefixedDenom).IBCDenom()

		providerRewards := providerBankKeeper.GetBalance(s.providerCtx(), rewardPool, prefixedDenom)

		// relay IBC transfer packet from consumer to provider
		// Note that relaying increases the pool rewards with the democracy consumers
		relayAllCommittedPackets(
			s,
			bundle.Chain,
			bundle.TransferPath,
			transfertypes.PortID,
			bundle.TransferPath.EndpointA.ChannelID,
			1,
		)

		// Check the provider received the rewards
		providerRewardsDelta := providerBankKeeper.GetBalance(s.providerCtx(), rewardPool, prefixedDenom).Sub(providerRewards)
		s.Require().True(providerRewardsDelta.Amount.GTE(pool.AmountOf(provIBCDenom)))
	}
}
