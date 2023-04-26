package integration

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	channeltypes "github.com/cosmos/ibc-go/v4/modules/core/04-channel/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	abci "github.com/tendermint/tendermint/abci/types"
)

// Tests the functionality of stopping a consumer chain at a higher level than unit tests
func (s *CCVTestSuite) TestStopConsumerChain() {
	providerKeeper := s.providerApp.GetProviderKeeper()
	providerStakingKeeper := s.providerApp.GetTestStakingKeeper()

	firstBundle := s.getFirstBundle()

	// choose a validator
	tmValidator := s.providerChain.Vals.Validators[0]
	valAddr, err := sdk.ValAddressFromHex(tmValidator.Address.String())
	s.Require().NoError(err)

	validator, found := providerStakingKeeper.GetValidator(s.providerCtx(), valAddr)
	s.Require().True(found)

	// get delegator address
	delAddr := s.providerChain.SenderAccount.GetAddress()

	// define variables required for test setup
	var (
		// bond amount
		bondAmt = sdk.NewInt(1000000)
		// number of unbonding operations performed
		ubdOpsNum = 4
		// store new shares created
		testShares sdk.Dec
	)

	// populate the provider chain states to setup the test using the following operations:
	// 	- setup CCV channel; establish CCV channel and set channelToChain, chainToChannel and initHeight mapping for the consumer chain ID
	// 	- delegate the total bond amount to the chosed validator
	// 	- undelegate the shares in four consecutive blocks evenly; create UnbondigOp and UnbondingOpIndex entries for the consumer chain ID
	// 	- set SlashAck state for the consumer chain ID
	setupOperations := []struct {
		fn func(suite *CCVTestSuite) error
	}{
		{
			func(suite *CCVTestSuite) error {
				suite.SetupAllCCVChannels()
				suite.SetupTransferChannel()
				return nil
			},
		},
		{
			func(suite *CCVTestSuite) error {
				testShares, err = providerStakingKeeper.Delegate(s.providerCtx(), delAddr, bondAmt, stakingtypes.Unbonded, validator, true)
				return err
			},
		},
		{
			func(suite *CCVTestSuite) error {
				for i := 0; i < ubdOpsNum; i++ {
					// undelegate one quarter of the shares
					_, err := providerStakingKeeper.Undelegate(s.providerCtx(), delAddr, valAddr, testShares.QuoInt64(int64(ubdOpsNum)))
					if err != nil {
						return err
					}
					// increment block
					s.providerChain.NextBlock()
				}
				return nil
			},
		},
		{
			func(suite *CCVTestSuite) error {
				providerKeeper.SetSlashAcks(s.providerCtx(), firstBundle.Chain.ChainID, []string{"validator-1", "validator-2", "validator-3"})
				providerKeeper.AppendPendingVSCPackets(s.providerCtx(), firstBundle.Chain.ChainID, ccv.ValidatorSetChangePacketData{ValsetUpdateId: 1})
				return nil
			},
		},
		{
			func(suite *CCVTestSuite) error {
				// Queue slash and vsc packet data for consumer 0, these queue entries will be removed
				firstBundle := s.getFirstBundle()
				globalEntry := ccv.NewGlobalSlashEntry(s.providerCtx().BlockTime(), firstBundle.Chain.ChainID, 7, ccv.ProviderConsAddress{})
				providerKeeper.QueueGlobalSlashEntry(s.providerCtx(), globalEntry)
				err := providerKeeper.QueueThrottledSlashPacketData(s.providerCtx(), firstBundle.Chain.ChainID, 1,
					ccv.SlashPacketData{ValsetUpdateId: 1})
				suite.Require().NoError(err)
				err = providerKeeper.QueueThrottledVSCMaturedPacketData(s.providerCtx(),
					firstBundle.Chain.ChainID, 2, ccv.VSCMaturedPacketData{ValsetUpdateId: 2})
				suite.Require().NoError(err)

				// Queue slash and vsc packet data for consumer 1, these queue entries will be not be removed
				secondBundle := s.getBundleByIdx(1)
				globalEntry = ccv.NewGlobalSlashEntry(s.providerCtx().BlockTime(), secondBundle.Chain.ChainID, 7, ccv.ProviderConsAddress{})
				providerKeeper.QueueGlobalSlashEntry(s.providerCtx(), globalEntry)
				err = providerKeeper.QueueThrottledSlashPacketData(s.providerCtx(), secondBundle.Chain.ChainID, 1,
					ccv.SlashPacketData{ValsetUpdateId: 1})
				suite.Require().NoError(err)
				err = providerKeeper.QueueThrottledVSCMaturedPacketData(s.providerCtx(),
					secondBundle.Chain.ChainID, 2, ccv.VSCMaturedPacketData{ValsetUpdateId: 2})
				suite.Require().NoError(err)

				return nil
			},
		},
	}

	for _, so := range setupOperations {
		err := so.fn(s)
		s.Require().NoError(err)
	}

	// stop the consumer chain
	err = providerKeeper.StopConsumerChain(s.providerCtx(), firstBundle.Chain.ChainID, true)
	s.Require().NoError(err)

	// check all states are removed and the unbonding operation released
	s.checkConsumerChainIsRemoved(firstBundle.Chain.ChainID, true)

	// check entries related to second consumer chain are not removed
	s.Require().Len(providerKeeper.GetAllGlobalSlashEntries(s.providerCtx()), 1)

	secondBundle := s.getBundleByIdx(1)
	slashData, vscMaturedData, _, _ := providerKeeper.GetAllThrottledPacketData(
		s.providerCtx(), secondBundle.Chain.ChainID)
	s.Require().Len(slashData, 1)
	s.Require().Len(vscMaturedData, 1)
}

// TODO Simon: implement OnChanCloseConfirm in IBC-GO testing to close the consumer chain's channel end
func (s *CCVTestSuite) TestStopConsumerOnChannelClosed() {
	// init the CCV channel states
	s.SetupCCVChannel(s.path)
	s.SetupTransferChannel()
	s.SendEmptyVSCPacket()

	providerKeeper := s.providerApp.GetProviderKeeper()

	// stop the consumer chain
	err := providerKeeper.StopConsumerChain(s.providerCtx(), s.consumerChain.ChainID, true)
	s.Require().NoError(err)

	err = s.path.EndpointA.UpdateClient()
	s.Require().NoError(err)

	// check that provider chain's channel end is closed
	s.Require().Equal(channeltypes.CLOSED, s.path.EndpointB.GetChannel().State)

	// simulate a relayer behaviour
	// err = s.path.EndpointA.OnChanCloseConfirm()
	// s.Require().NoError(err)

	// expect to panic in consumer chain's BeginBlock due to the above
	// s.consumerChain.NextBlock()

	// check that the provider's channel is removed
	// _, found := s.consumerApp.GetConsumerKeeper().GetProviderChannel(s.consumerCtx())
	// s.Require().False(found)
}

func (s *CCVTestSuite) checkConsumerChainIsRemoved(chainID string, checkChannel bool) {
	channelID := s.path.EndpointB.ChannelID
	providerKeeper := s.providerApp.GetProviderKeeper()
	providerStakingKeeper := s.providerApp.GetTestStakingKeeper()

	if checkChannel {
		// check channel's state is closed
		s.Require().Equal(channeltypes.CLOSED, s.path.EndpointB.GetChannel().State)
	}

	// check UnbondingOps were deleted and undelegation entries aren't onHold
	for _, unbondingOpsIndex := range providerKeeper.GetAllUnbondingOpIndexes(s.providerCtx(), chainID) {
		_, found := providerKeeper.GetUnbondingOpIndex(s.providerCtx(), chainID, unbondingOpsIndex.VscId)
		s.Require().False(found)
		for _, ubdID := range unbondingOpsIndex.UnbondingOpIds {
			_, found = providerKeeper.GetUnbondingOp(s.providerCtx(), unbondingOpsIndex.UnbondingOpIds[ubdID])
			s.Require().False(found)
			ubd, _ := providerStakingKeeper.GetUnbondingDelegationByUnbondingID(s.providerCtx(), unbondingOpsIndex.UnbondingOpIds[ubdID])
			s.Require().Zero(ubd.Entries[ubdID].UnbondingOnHoldRefCount)
		}
	}

	// verify consumer chain's states are removed
	_, found := providerKeeper.GetConsumerGenesis(s.providerCtx(), chainID)
	s.Require().False(found)
	_, found = providerKeeper.GetConsumerClientId(s.providerCtx(), chainID)
	s.Require().False(found)

	_, found = providerKeeper.GetChainToChannel(s.providerCtx(), chainID)
	s.Require().False(found)

	_, found = providerKeeper.GetChannelToChain(s.providerCtx(), channelID)
	s.Require().False(found)

	s.Require().Nil(providerKeeper.GetSlashAcks(s.providerCtx(), chainID))
	s.Require().Zero(providerKeeper.GetInitChainHeight(s.providerCtx(), chainID))
	s.Require().Empty(providerKeeper.GetPendingVSCPackets(s.providerCtx(), chainID))

	// No remaining global entries for this consumer
	allGlobalEntries := providerKeeper.GetAllGlobalSlashEntries(s.providerCtx())
	for _, entry := range allGlobalEntries {
		s.Require().NotEqual(chainID, entry.ConsumerChainID)
	}

	// No remaining per-chain entries for this consumer
	slashData, vscMaturedData, _, _ := providerKeeper.GetAllThrottledPacketData(s.providerCtx(), chainID)
	s.Require().Empty(slashData)
	s.Require().Empty(vscMaturedData)
}

// TestProviderChannelClosed checks that a consumer chain panics
// when the provider channel was established and then closed
func (suite *CCVTestSuite) TestProviderChannelClosed() {
	suite.SetupCCVChannel(suite.path)
	// establish provider channel with a first VSC packet
	suite.SendEmptyVSCPacket()

	consumerKeeper := suite.consumerApp.GetConsumerKeeper()

	channelID, found := consumerKeeper.GetProviderChannel(suite.consumerChain.GetContext())
	suite.Require().True(found)

	// close provider channel
	err := consumerKeeper.ChanCloseInit(suite.consumerChain.GetContext(), ccv.ConsumerPortID, channelID)
	suite.Require().NoError(err)
	suite.Require().True(consumerKeeper.IsChannelClosed(suite.consumerChain.GetContext(), channelID))

	// assert begin blocker did panics
	defer func() {
		if r := recover(); r != nil {
			return
		}
		suite.Require().Fail("Begin blocker did not panic with a closed channel")
	}()
	suite.consumerApp.BeginBlocker(suite.consumerChain.GetContext(), abci.RequestBeginBlock{})
}
