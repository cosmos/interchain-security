package integration

import (
	"strings"

	"cosmossdk.io/math"
	abci "github.com/cometbft/cometbft/abci/types"
	"github.com/cometbft/cometbft/libs/bytes"
	distrtypes "github.com/cosmos/cosmos-sdk/x/distribution/types"
	transfertypes "github.com/cosmos/ibc-go/v7/modules/apps/transfer/types"
	clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v7/modules/core/04-channel/types"

	sdk "github.com/cosmos/cosmos-sdk/types"
	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"

	ibctransfertypes "github.com/cosmos/ibc-go/v7/modules/apps/transfer/types"
	icstestingutils "github.com/cosmos/interchain-security/v4/testutil/integration"
	consumerkeeper "github.com/cosmos/interchain-security/v4/x/ccv/consumer/keeper"
	consumertypes "github.com/cosmos/interchain-security/v4/x/ccv/consumer/types"
	providerkeeper "github.com/cosmos/interchain-security/v4/x/ccv/provider/keeper"
	"github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
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
	providerAccountKeeper := s.providerApp.GetTestAccountKeeper()
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
	rewardPool := providerAccountKeeper.GetModuleAccount(s.providerCtx(), providertypes.ConsumerRewardsPool).GetAddress()
	rewardCoins := providerBankKeeper.GetAllBalances(s.providerCtx(), rewardPool)

	ibcCoinIndex := -1
	for i, coin := range rewardCoins {
		if strings.HasPrefix(coin.Denom, "ibc") {
			ibcCoinIndex = i
		}
	}

	// Check that we found an ibc denom in the reward pool
	s.Require().Greater(ibcCoinIndex, -1)

	// Check that the coins got into the ConsumerRewardsPool
	s.Require().Equal(rewardCoins[ibcCoinIndex].Amount, (providerExpectedRewards[0].Amount))

	// Advance a block and check that the coins are still in the ConsumerRewardsPool
	s.providerChain.NextBlock()
	rewardCoins = providerBankKeeper.GetAllBalances(s.providerCtx(), rewardPool)
	s.Require().Equal(rewardCoins[ibcCoinIndex].Amount, (providerExpectedRewards[0].Amount))

	// Set the consumer reward denom. This would be done by a governance proposal in prod
	s.providerApp.GetProviderKeeper().SetConsumerRewardDenom(s.providerCtx(), rewardCoins[ibcCoinIndex].Denom)

	// Refill the consumer fee pool
	err = consumerBankKeeper.SendCoinsFromAccountToModule(s.consumerCtx(), s.consumerChain.SenderAccount.GetAddress(), authtypes.FeeCollectorName, fees)
	s.Require().NoError(err)

	// pass two blocks
	s.consumerChain.NextBlock()
	s.consumerChain.NextBlock()

	// transfer rewards from consumer to provider
	relayAllCommittedPackets(s, s.consumerChain, s.transferPath, transfertypes.PortID, s.transferPath.EndpointA.ChannelID, 1)

	// check that the consumer rewards allocation are empty since relayAllCommittedPackets call BeginBlock
	rewardsAlloc := s.providerApp.GetProviderKeeper().GetConsumerRewardsAllocation(s.providerCtx(), s.consumerChain.ChainID)
	s.Require().Empty(rewardsAlloc.Rewards)

	// Check that the reward pool still has the first coins transferred that were never allocated
	rewardCoins = providerBankKeeper.GetAllBalances(s.providerCtx(), rewardPool)
	s.Require().Equal(rewardCoins[ibcCoinIndex].Amount, (providerExpectedRewards[0].Amount))

	// check that the fee pool has the expected amount of coins
	// Note that all rewards are allocated to the community pool since
	// BeginBlock is called without the validators' votes in ibctesting.
	// See NextBlock() in https://github.com/cosmos/ibc-go/blob/release/v7.3.x/testing/chain.go#L281
	communityCoins := s.providerApp.GetTestDistributionKeeper().GetFeePoolCommunityCoins(s.providerCtx())
	s.Require().Equal(communityCoins[ibcCoinIndex].Amount, (sdk.NewDecCoinFromCoin(providerExpectedRewards[0]).Amount))
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

// TestIBCTransferMiddleware tests the logic of the IBC transfer OnRecvPacket callback
func (s *CCVTestSuite) TestIBCTransferMiddleware() {

	var (
		data        ibctransfertypes.FungibleTokenPacketData
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

			cbs, ok := s.providerChain.App.GetIBCKeeper().Router.GetRoute(ibctransfertypes.ModuleName)
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

	chainID := "consumer"
	validators := []bytes.HexBytes{
		s.providerChain.Vals.Validators[0].Address,
		s.providerChain.Vals.Validators[1].Address,
	}
	votes := []abci.VoteInfo{
		{Validator: abci.Validator{Address: validators[0], Power: 1}},
		{Validator: abci.Validator{Address: validators[1], Power: 1}},
	}

	testCases := []struct {
		name         string
		votes        []abci.VoteInfo
		tokens       sdk.DecCoins
		expAllocated sdk.DecCoins
	}{
		{
			name: "tokens are empty",
		},
		{
			name:         "total voting power is zero",
			tokens:       sdk.DecCoins{sdk.NewDecCoin(sdk.DefaultBondDenom, math.NewInt(100_000))},
			expAllocated: nil,
		},
		{
			name:         "expect all tokens to be allocated to a single validator",
			votes:        []abci.VoteInfo{votes[0]},
			tokens:       sdk.DecCoins{sdk.NewDecCoin(sdk.DefaultBondDenom, math.NewInt(999))},
			expAllocated: sdk.DecCoins{sdk.NewDecCoin(sdk.DefaultBondDenom, math.NewInt(999))},
		},
		{
			name:         "expect tokens to be allocated evenly between validators",
			votes:        []abci.VoteInfo{votes[0], votes[1]},
			tokens:       sdk.DecCoins{sdk.NewDecCoinFromDec(sdk.DefaultBondDenom, math.LegacyNewDecFromIntWithPrec(math.NewInt(999), 3))},
			expAllocated: sdk.DecCoins{sdk.NewDecCoinFromDec(sdk.DefaultBondDenom, math.LegacyNewDecFromIntWithPrec(math.NewInt(999), 3))},
		},
	}

	// opt the validators in to verify that they charge
	// to their delegators the custom commission for the consumer chain
	for _, v := range s.providerChain.Vals.Validators {
		consAddr := sdk.ConsAddress(v.Address)
		provAddr := providertypes.NewProviderConsAddress(consAddr)

		val, found := s.providerApp.GetTestStakingKeeper().GetValidatorByConsAddr(s.providerCtx(), consAddr)
		s.Require().True(found)

		// check that no commission is set for the validator
		s.Require().Equal(val.Commission.Rate, math.LegacyZeroDec())

		// opt the validators in consumer with a custom commission of 100%
		providerKeeper.SetOptedIn(
			s.providerCtx(),
			chainID,
			types.OptedInValidator{
				ProviderAddr:   provAddr.Address,
				BlockHeight:    s.providerCtx().BlockHeight(),
				PublicKey:      v.PubKey.Bytes(),
				CommissionRate: "1",
			},
		)
	}

	for _, tc := range testCases {
		s.Run(tc.name, func() {
			// TODO: opt validators in and verify
			// that rewards are only allocated to them
			ctx, _ := s.providerCtx().CacheContext()

			// allocate tokens
			res := providerKeeper.AllocateTokensToConsumerValidators(
				ctx,
				chainID,
				tc.votes,
				tc.tokens,
			)

			// check that the expected result is returned
			s.Require().Equal(tc.expAllocated, res)

			if !tc.expAllocated.Empty() {
				// rewards are expected to be allocated evenly between validators
				rewardsPerVal := tc.expAllocated.QuoDec(sdk.NewDec(int64(len(tc.votes))))

				// check that the rewards are allocated to validators
				for _, v := range tc.votes {
					valAddr := sdk.ValAddress(v.Validator.Address)
					rewards := s.providerApp.GetTestDistributionKeeper().GetValidatorOutstandingRewards(
						ctx,
						valAddr,
					)
					s.Require().Equal(rewardsPerVal, rewards.Rewards)

					// send tokens to the distribution module to allow the rewards withdrawing
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
					s.Require().Equal(withdrawnCoins, valRewardsTrunc)
				}
			} else {
				for _, v := range tc.votes {
					valAddr := sdk.ValAddress(v.Validator.Address)
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
