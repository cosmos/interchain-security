package integration

import (
	"strings"

	transfertypes "github.com/cosmos/ibc-go/v7/modules/apps/transfer/types"
	clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v7/modules/core/04-channel/types"

	"cosmossdk.io/math"

	sdk "github.com/cosmos/cosmos-sdk/types"
	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"
	distrtypes "github.com/cosmos/cosmos-sdk/x/distribution/types"

	abci "github.com/cometbft/cometbft/abci/types"

	icstestingutils "github.com/cosmos/interchain-security/v4/testutil/integration"
	consumerkeeper "github.com/cosmos/interchain-security/v4/x/ccv/consumer/keeper"
	consumertypes "github.com/cosmos/interchain-security/v4/x/ccv/consumer/types"
	providerkeeper "github.com/cosmos/interchain-security/v4/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
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
	s.nextEpoch()

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
	providerAccountKeeper := s.providerApp.GetTestAccountKeeper()
	consumerBankKeeper := s.consumerApp.GetTestBankKeeper()
	providerBankKeeper := s.providerApp.GetTestBankKeeper()
	providerKeeper := s.providerApp.GetProviderKeeper()
	providerDistributionKeeper := s.providerApp.GetTestDistributionKeeper()

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
		for _, v := range providerKeeper.GetConsumerValSet(ctx, s.consumerChain.ChainID) {
			val, ok := s.providerApp.GetTestStakingKeeper().GetValidatorByConsAddr(ctx, sdk.ConsAddress(v.ProviderConsAddr))
			s.Require().True(ok)
			valReward := providerDistributionKeeper.GetValidatorOutstandingRewards(ctx, val.GetOperator())
			totalRewards = totalRewards.Add(valReward.Rewards...)
		}
		return totalRewards
	}
	consuValsRewards := consumerValsOutstandingRewardsFunc(s.providerCtx())

	// Save community pool balance
	communityPool := providerDistributionKeeper.GetFeePoolCommunityCoins(s.providerCtx())

	// Transfer rewards from consumer to provider
	relayAllCommittedPackets(
		s,
		s.consumerChain,
		s.transferPath,
		transfertypes.PortID,
		s.transferPath.EndpointA.ChannelID,
		1,
	)

	// Check that the consumer rewards allocation are empty since relayAllCommittedPackets calls BeginBlockRD,
	// which in turns calls AllocateTokens.
	rewardsAlloc := providerKeeper.GetConsumerRewardsAllocation(s.providerCtx(), s.consumerChain.ChainID)
	s.Require().Empty(rewardsAlloc.Rewards)

	// Check that the reward pool still holds the coins from the first transfer,
	// which were never allocated since they were not whitelisted
	rewardCoins = providerBankKeeper.GetAllBalances(s.providerCtx(), rewardPool)
	s.Require().Equal(rewardCoins.AmountOf(rewardsIBCdenom), providerExpRewardsAmount)

	// Check that summing the rewards received by the consumer validators and the community pool
	// is equal to the expected provider rewards
	consuValsRewardsReceived := consumerValsOutstandingRewardsFunc(s.providerCtx()).Sub(consuValsRewards)
	communityPoolDelta := providerDistributionKeeper.GetFeePoolCommunityCoins(s.providerCtx()).Sub(communityPool)

	s.Require().Equal(
		sdk.NewDecFromInt(providerExpRewardsAmount),
		consuValsRewardsReceived.AmountOf(rewardsIBCdenom).Add(communityPoolDelta.AmountOf(rewardsIBCdenom)),
	)
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
			amount := sdk.NewInt(100)

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

	totalRewards := sdk.Coins{sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(100))}

	// fund consumer rewards pool
	bankKeeper.SendCoinsFromAccountToModule(
		s.providerCtx(),
		s.providerChain.SenderAccount.GetAddress(),
		providertypes.ConsumerRewardsPool,
		totalRewards,
	)

	// Allocate rewards evenly between consumers
	rewardsPerConsumer := totalRewards.QuoInt(math.NewInt(int64(len(s.consumerBundles))))
	for chainID := range s.consumerBundles {
		// update consumer allocation
		providerKeeper.SetConsumerRewardsAllocation(
			s.providerCtx(),
			chainID,
			providertypes.ConsumerRewardsAllocation{
				Rewards: sdk.NewDecCoinsFromCoins(rewardsPerConsumer...),
			},
		)
	}

	// Iterate over the validators and
	// store their current voting power and outstanding rewards
	lastValOutRewards := map[string]sdk.DecCoins{}
	votes := []abci.VoteInfo{}
	for _, val := range s.providerChain.Vals.Validators {
		votes = append(votes,
			abci.VoteInfo{
				Validator:       abci.Validator{Address: val.Address, Power: val.VotingPower},
				SignedLastBlock: true,
			},
		)

		valRewards := distributionKeeper.GetValidatorOutstandingRewards(s.providerCtx(), sdk.ValAddress(val.Address))
		lastValOutRewards[sdk.ValAddress(val.Address).String()] = valRewards.Rewards
	}

	// store community pool balance
	lastCommPool := distributionKeeper.GetFeePoolCommunityCoins(s.providerCtx())

	// execute BeginBlock to trigger the token allocation
	providerKeeper.BeginBlockRD(
		s.providerCtx(),
		abci.RequestBeginBlock{
			LastCommitInfo: abci.CommitInfo{
				Votes: votes,
			},
		},
	)

	valNum := len(s.providerChain.Vals.Validators)
	consuNum := len(s.consumerBundles)

	// compute the expected validators token allocation by subtracting the community tax
	rewardsPerConsumerDec := sdk.NewDecCoinsFromCoins(rewardsPerConsumer...)
	communityTax := distributionKeeper.GetCommunityTax(s.providerCtx())
	validatorsExpRewards := rewardsPerConsumerDec.
		MulDecTruncate(math.LegacyOneDec().Sub(communityTax)).
		// multiply by the number of consumers since all the validators opted in
		MulDec(sdk.NewDec(int64(consuNum)))
	perValExpReward := validatorsExpRewards.QuoDec(sdk.NewDec(int64(valNum)))

	// verify the validator tokens allocation
	// note that the validators have the same voting power to keep things simple
	for _, val := range s.providerChain.Vals.Validators {
		valRewards := distributionKeeper.GetValidatorOutstandingRewards(s.providerCtx(), sdk.ValAddress(val.Address))
		s.Require().Equal(
			valRewards.Rewards,
			lastValOutRewards[sdk.ValAddress(val.Address).String()].Add(perValExpReward...),
		)
	}

	commPoolExpRewards := sdk.NewDecCoinsFromCoins(totalRewards...).Sub(validatorsExpRewards)
	currCommPool := distributionKeeper.GetFeePoolCommunityCoins(s.providerCtx())

	s.Require().Equal(currCommPool, (lastCommPool.Add(commPoolExpRewards...)))
}

// TestAllocateTokens is a unit-test for TransferConsumerRewardsToDistributionModule()
// but is written as an integration test to avoid excessive mocking.
func (s *CCVTestSuite) TransferConsumerRewardsToDistributionModule() {
	testCases := []struct {
		name         string
		rewardsPool  sdk.Coins
		rewardsAlloc sdk.DecCoins
		expErr       bool
	}{
		{
			"empty consumer rewards pool",
			sdk.Coins{},
			sdk.DecCoins{},
			false,
		},
		{
			"empty consumer allocation",
			sdk.Coins{
				sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(100)),
			},
			sdk.DecCoins{},
			false,
		},
		{
			"equal consumer rewards pool and allocation",
			sdk.Coins{
				sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(100)),
			},
			sdk.DecCoins{
				sdk.NewDecCoin(sdk.DefaultBondDenom, sdk.NewInt(100)),
			},
			false,
		},
		{
			"less consumer rewards than allocation",
			sdk.Coins{
				sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(90)),
			},
			sdk.DecCoins{
				sdk.NewDecCoin(sdk.DefaultBondDenom, sdk.NewInt(100)),
			},
			true,
		},
		{
			"remaining consumer rewards allocation",
			sdk.Coins{
				sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(100)),
			},
			sdk.DecCoins{
				sdk.DecCoin{
					Denom:  sdk.DefaultBondDenom,
					Amount: sdk.NewDecWithPrec(995, 1),
				},
			},
			false,
		},
	}

	providerKeeper := s.providerApp.GetProviderKeeper()
	bankKeeper := s.providerApp.GetTestBankKeeper()
	distributionKeeper := s.providerApp.GetTestDistributionKeeper()

	chainID := s.consumerChain.ChainID

	for _, tc := range testCases {
		s.Run(tc.name, func() {
			ctx, _ := s.providerCtx().CacheContext()
			// fund consumer rewards pool
			bankKeeper.SendCoinsFromAccountToModule(
				ctx,
				s.providerChain.SenderAccount.GetAddress(),
				providertypes.ConsumerRewardsPool,
				tc.rewardsPool,
			)

			// update consumer rewars allocation
			providerKeeper.SetConsumerRewardsAllocation(
				ctx,
				chainID,
				providertypes.ConsumerRewardsAllocation{
					Rewards: tc.rewardsAlloc,
				},
			)

			// store pool balance
			oldPool := bankKeeper.GetAllBalances(
				ctx,
				distributionKeeper.GetDistributionAccount(ctx).GetAddress(),
			)

			// transfer consumer rewars to distribution module
			coinsTransferred, err := providerKeeper.TransferConsumerRewardsToDistributionModule(
				ctx,
				chainID,
			)
			if tc.expErr {
				s.Require().Error(err)
				return
			}

			// check remaining consumer rewards allocation
			expCoinTransferred, expRemaining := tc.rewardsAlloc.TruncateDecimal()
			s.Require().Equal(expCoinTransferred, coinsTransferred)

			s.Require().Equal(
				expRemaining,
				providerKeeper.GetConsumerRewardsAllocation(ctx, chainID).Rewards,
			)

			// check updated consuemer rewards pool balance
			newPool := bankKeeper.GetAllBalances(
				ctx,
				distributionKeeper.GetDistributionAccount(ctx).GetAddress(),
			)

			s.Require().Equal(newPool.Sub(oldPool...), coinsTransferred)
		})
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

func (s *CCVTestSuite) TestAllocateTokensToValidator() {
	providerKeeper := s.providerApp.GetProviderKeeper()
	distributionKeeper := s.providerApp.GetTestDistributionKeeper()
	bankKeeper := s.providerApp.GetTestBankKeeper()

	chainID := s.consumerChain.ChainID

	testCases := []struct {
		name         string
		consuValLen  int
		tokens       sdk.DecCoins
		rate         sdk.Dec
		expAllocated sdk.DecCoins
	}{
		{
			name:         "tokens are empty",
			tokens:       sdk.DecCoins{},
			rate:         sdk.ZeroDec(),
			expAllocated: nil,
		},
		{
			name:         "consumer valset is empty - total voting power is zero",
			tokens:       sdk.DecCoins{sdk.NewDecCoin(sdk.DefaultBondDenom, math.NewInt(100_000))},
			rate:         sdk.ZeroDec(),
			expAllocated: nil,
		},
		{
			name:         "expect all tokens to be allocated to a single validator",
			consuValLen:  1,
			tokens:       sdk.DecCoins{sdk.NewDecCoin(sdk.DefaultBondDenom, math.NewInt(999))},
			rate:         sdk.NewDecWithPrec(5, 1),
			expAllocated: sdk.DecCoins{sdk.NewDecCoin(sdk.DefaultBondDenom, math.NewInt(999))},
		},
		{
			name:         "expect tokens to be allocated evenly between validators",
			consuValLen:  2,
			tokens:       sdk.DecCoins{sdk.NewDecCoinFromDec(sdk.DefaultBondDenom, math.LegacyNewDecFromIntWithPrec(math.NewInt(999), 2))},
			rate:         sdk.OneDec(),
			expAllocated: sdk.DecCoins{sdk.NewDecCoinFromDec(sdk.DefaultBondDenom, math.LegacyNewDecFromIntWithPrec(math.NewInt(999), 2))},
		},
	}

	for _, tc := range testCases {
		s.Run(tc.name, func() {
			ctx, _ := s.providerCtx().CacheContext()

			// change the consumer valset
			consuVals := providerKeeper.GetConsumerValSet(ctx, chainID)
			providerKeeper.DeleteConsumerValSet(ctx, chainID)
			providerKeeper.SetConsumerValSet(ctx, chainID, consuVals[0:tc.consuValLen])
			consuVals = providerKeeper.GetConsumerValSet(ctx, chainID)

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
				rewardsPerVal := tc.expAllocated.QuoDec(sdk.NewDec(int64(len(consuVals))))

				// check that the rewards are allocated to validators
				for _, v := range consuVals {
					valAddr := sdk.ValAddress(v.ProviderConsAddr)
					rewards := s.providerApp.GetTestDistributionKeeper().GetValidatorOutstandingRewards(
						ctx,
						valAddr,
					)
					s.Require().Equal(rewardsPerVal, rewards.Rewards)

					// send rewards to the distribution module
					valRewardsTrunc, _ := rewards.Rewards.TruncateDecimal()
					err := bankKeeper.SendCoinsFromAccountToModule(
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
					rewards := s.providerApp.GetTestDistributionKeeper().GetValidatorOutstandingRewards(
						ctx,
						valAddr,
					)
					s.Require().Zero(rewards.Rewards)
				}
			}
		})
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

	totalConsumerRewards := sdk.Coins{}

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
		if pool := bankKeeper.GetAllBalances(
			bundle.GetCtx(),
			accountKeeper.GetModuleAccount(bundle.GetCtx(), consumertypes.ConsumerToSendToProviderName).GetAddress(),
		); pool.Empty() {
			// if pool is empty, fill it with some tokens
			rewardsPerConsumer = sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(100))
			err := bankKeeper.SendCoinsFromAccountToModule(
				bundle.GetCtx(),
				bundle.Chain.SenderAccount.GetAddress(),
				consumertypes.ConsumerToSendToProviderName,
				sdk.NewCoins(rewardsPerConsumer),
			)
			s.Require().NoError(err)
		} else {
			// execute the internal rewards distribution
			// to save the pool's balance before
			// it gets transferred to the provider in EndBlock
			consumerKeeper.DistributeRewardsInternally(bundle.GetCtx())
			pool = bankKeeper.GetAllBalances(
				bundle.GetCtx(),
				accountKeeper.GetModuleAccount(bundle.GetCtx(), consumertypes.ConsumerToSendToProviderName).GetAddress(),
			)
			s.Require().Len(pool, 1, "consumer reward pool cannot have multiple token denoms")
			rewardsPerConsumer = pool[0]
		}

		// perform the reward transfer
		bundle.Chain.NextBlock()

		// relay IBC transfer packet from consumer to provider
		relayAllCommittedPackets(
			s,
			bundle.Chain,
			bundle.TransferPath,
			transfertypes.PortID,
			bundle.TransferPath.EndpointA.ChannelID,
			1,
		)

		// construct the denom of the reward tokens for the provider
		prefixedDenom := transfertypes.GetPrefixedDenom(
			transfertypes.PortID,
			bundle.TransferPath.EndpointB.ChannelID,
			rewardsPerConsumer.Denom,
		)
		provIBCDenom := transfertypes.ParseDenomTrace(prefixedDenom).IBCDenom()

		// sum the total rewards transferred to the provider
		totalConsumerRewards = totalConsumerRewards.
			Add(sdk.NewCoin(provIBCDenom, rewardsPerConsumer.Amount))
	}

	// Check that the provider receives the rewards of each consumer
	rewardCoins = providerBankKeeper.GetAllBalances(s.providerCtx(), rewardPool)
	s.Require().Equal(totalConsumerRewards, rewardCoins, totalConsumerRewards.String(), rewardCoins.String())
}
