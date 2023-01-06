package e2e

import (
	"fmt"
	"strings"

	sdk "github.com/cosmos/cosmos-sdk/types"
	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"
	transfertypes "github.com/cosmos/ibc-go/v3/modules/apps/transfer/types"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
)

// This test is valid for minimal viable consumer chain
func (s *CCVTestSuite) TestRewardsDistribution() {

	//set up channel and delegate some tokens in order for validator set update to be sent to the consumer chain
	s.SetupCCVChannel(s.path)
	s.SetupTransferChannel()
	bondAmt := sdk.NewInt(10000000)
	delAddr := s.providerChain.SenderAccount.GetAddress()
	delegate(s, delAddr, bondAmt)
	s.providerChain.NextBlock()

	// relay VSC packets from provider to consumer
	relayAllCommittedPackets(s, s.providerChain, s.path, ccv.ProviderPortID, s.path.EndpointB.ChannelID, 1)

	//reward for the provider chain will be sent after each 2 blocks
	consumerParams := s.consumerApp.GetSubspace(consumertypes.ModuleName)
	consumerParams.Set(s.consumerCtx(), consumertypes.KeyBlocksPerDistributionTransmission, int64(2))
	s.consumerChain.NextBlock()

	consumerAccountKeeper := s.consumerApp.GetE2eAccountKeeper()
	consumerBankKeeper := s.consumerApp.GetE2eBankKeeper()

	//send coins to the fee pool which is used for reward distribution
	consumerFeePoolAddr := consumerAccountKeeper.GetModuleAccount(s.consumerCtx(), authtypes.FeeCollectorName).GetAddress()
	feePoolTokensOld := consumerBankKeeper.GetAllBalances(s.consumerCtx(), consumerFeePoolAddr)
	fees := sdk.NewCoins(sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(100)))
	err := consumerBankKeeper.SendCoinsFromAccountToModule(s.consumerCtx(), s.consumerChain.SenderAccount.GetAddress(), authtypes.FeeCollectorName, fees)
	s.Require().NoError(err)
	feePoolTokens := consumerBankKeeper.GetAllBalances(s.consumerCtx(), consumerFeePoolAddr)
	s.Require().Equal(sdk.NewInt(100).Add(feePoolTokensOld.AmountOf(sdk.DefaultBondDenom)), feePoolTokens.AmountOf(sdk.DefaultBondDenom))

	//calculate the reward for consumer and provider chain. Consumer will receive ConsumerRedistributeFrac, the rest is going to provider
	frac, err := sdk.NewDecFromStr(s.consumerApp.GetConsumerKeeper().GetConsumerRedistributionFrac(s.consumerCtx()))
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
	providerRedistributeAddr := consumerAccountKeeper.GetModuleAccount(s.consumerCtx(), consumertypes.ConsumerToSendToProviderName).GetAddress()
	providerTokens := consumerBankKeeper.GetAllBalances(s.consumerCtx(), providerRedistributeAddr)
	s.Require().Equal(providerExpectedRewards.AmountOf(sdk.DefaultBondDenom), providerTokens.AmountOf(sdk.DefaultBondDenom))

	//send the reward to provider chain after 2 blocks

	s.consumerChain.NextBlock()
	providerTokens = consumerBankKeeper.GetAllBalances(s.consumerCtx(), providerRedistributeAddr)
	s.Require().Equal(0, len(providerTokens))

	relayAllCommittedPackets(s, s.consumerChain, s.transferPath, transfertypes.PortID, s.transferPath.EndpointA.ChannelID, 1)
	s.providerChain.NextBlock()
	communityCoins := s.providerApp.GetE2eDistributionKeeper().GetFeePoolCommunityCoins(s.providerCtx())
	ibcCoinIndex := -1
	for i, coin := range communityCoins {
		if strings.HasPrefix(coin.Denom, "ibc") {
			ibcCoinIndex = i
		}
	}
	s.Require().Greater(ibcCoinIndex, -1)
	s.Require().True(communityCoins[ibcCoinIndex].Amount.Equal(sdk.NewDecCoinFromCoin(providerExpectedRewards[0]).Amount))
}

// TestEndBlockRD tests that the last transmission block height (LTBH) is correctly updated after the expected
// number of block have passed. It also checks that the IBC transfer transfer states are discarded if
// the reward distribution to the provider has failed.
func (s *CCVTestSuite) TestEndBlockRD() {
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
	consumerBankKeeper := s.consumerApp.GetE2eBankKeeper()

	bpdt := consumerKeeper.GetBlocksPerDistributionTransmission(s.consumerCtx())
	transChanID := s.consumerApp.GetConsumerKeeper().GetDistributionTransmissionChannel(s.consumerCtx())

	// corruptTransChannel intentionally causes the reward distribution to fail by corrupting the transmission,
	// causing the SendPacket function to return an error.
	// Note that the Transferkeeper sends the outgoing fees to an escrow address BEFORE the reward distribution
	// is aborted within the SendPacket function.
	corruptTransChannel := func(ctx sdk.Context) {
		tChan, _ := s.consumerApp.GetIBCKeeper().ChannelKeeper.GetChannel(ctx, transfertypes.PortID, transChanID)
		tChan.Counterparty.PortId = "invalid/PortID"
		s.consumerApp.GetIBCKeeper().ChannelKeeper.SetChannel(ctx, transfertypes.PortID, transChanID, tChan)
	}

	// prepareRD pass enough blocks in order that the reward distribution is triggered in
	// the next consumer EndBlock and allocate some coins to the fee pool
	prepareRD := func(ctx sdk.Context) {
		// make sure we pass enough block
		s.coordinator.CommitNBlocks(s.consumerChain, uint64(bpdt))
		// fill pool
		fees := sdk.NewCoins(sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(100)))
		err := consumerBankKeeper.SendCoinsFromAccountToModule(ctx, s.consumerChain.SenderAccount.GetAddress(), authtypes.FeeCollectorName, fees)
		s.Require().NoError(err)
	}

	// lBThUpdated checks that the current LBTH is greater than the given block height
	lBThUpdated := func(ctx sdk.Context, height int64) bool {
		return height < consumerKeeper.GetLastTransmissionBlockHeight(ctx).Height
	}

	// getEscrowBalance gets the current balances in the escrow account holding the transfered tokens to the provider
	getEscrowBalance := func(ctx sdk.Context) sdk.Coins {
		escAddr := transfertypes.GetEscrowAddress(transfertypes.PortID, transChanID)
		return s.consumerApp.GetE2eBankKeeper().GetAllBalances(ctx, escAddr)
	}

	testCases := []struct {
		name               string
		setup              func(ctx sdk.Context)
		expLBThUpdated     bool
		expStatesPersisted bool
	}{{
		name:               fmt.Sprintf("should not update LBTH before %d block are passed", bpdt),
		setup:              func(sdk.Context) {},
		expLBThUpdated:     false,
		expStatesPersisted: false,
	}, {
		name: fmt.Sprintf("should update LBTH when %d or more block are passed", bpdt),
		setup: func(ctx sdk.Context) {
			prepareRD(ctx)
		},
		expLBThUpdated:     true,
		expStatesPersisted: true,
	}, {
		name: "should update LBTH and discard the IBC transfer states when sending rewards to provider fails",
		setup: func(ctx sdk.Context) {
			prepareRD(ctx)
			corruptTransChannel(ctx)
		},
		expLBThUpdated:     true,
		expStatesPersisted: false,
	},
	}

	// reward for the provider chain will be sent after each 2 blocks
	consumerParams := s.consumerApp.GetSubspace(consumertypes.ModuleName)
	consumerParams.Set(s.consumerCtx(), consumertypes.KeyBlocksPerDistributionTransmission, int64(2))

	for _, tc := range testCases {
		s.Run(tc.name, func() {
			ctx := s.consumerCtx()
			oldLbth := consumerKeeper.GetLastTransmissionBlockHeight(ctx)
			oldEscBalance := getEscrowBalance(ctx)

			// prepare the RD if we expect LTHB to be updated
			if tc.expLBThUpdated {
				prepareRD(ctx)
				// make the RD fail to check that the states aren't persisted
				if !tc.expStatesPersisted {
					corruptTransChannel(ctx)
				}
			}

			// trigger RD in EndBlockRD
			s.consumerChain.NextBlock()

			switch {
			case tc.expLBThUpdated:
				s.Require().True(lBThUpdated(s.consumerCtx(), oldLbth.Height))

			case tc.expStatesPersisted:
				// check that the coins present on the escrow account balance are updated
				currentEscrowBalance := getEscrowBalance(ctx)
				s.Require().NotEqual(currentEscrowBalance, oldEscBalance)

			case !tc.expStatesPersisted:
				// check that the coins present on the escrow account balance aren't updated
				currentEscrowBalance := getEscrowBalance(ctx)
				s.Require().Equal(currentEscrowBalance, oldEscBalance)
			}
		})
	}
}
