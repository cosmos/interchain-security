package e2e

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	abci "github.com/tendermint/tendermint/abci/types"
)

// Tests the functionality of stopping a consumer chain at a higher level than unit tests
func (s *CCVTestSuite) TestStopConsumerChain() {

	providerKeeper := s.providerApp.GetProviderKeeper()
	providerStakingKeeper := s.providerApp.GetE2eStakingKeeper()

	// default consumer chain ID
	consumerChainID := s.consumerChain.ChainID

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
	// 	- set SlashAck and LockUnbondingOnTimeout states for the consumer chain ID
	setupOperations := []struct {
		fn func(suite *CCVTestSuite) error
	}{
		{
			func(suite *CCVTestSuite) error {
				suite.SetupCCVChannel()
				suite.SetupTransferChannel()
				return nil
			},
		},
		{
			func(suite *CCVTestSuite) error {
				testShares, err = providerStakingKeeper.Delegate(s.providerCtx(), delAddr, bondAmt, stakingtypes.Unbonded, stakingtypes.Validator(validator), true)
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
				providerKeeper.SetSlashAcks(s.providerCtx(), consumerChainID, []string{"validator-1", "validator-2", "validator-3"})
				providerKeeper.SetLockUnbondingOnTimeout(s.providerCtx(), consumerChainID)
				providerKeeper.AppendPendingVSC(s.providerCtx(), consumerChainID, ccv.ValidatorSetChangePacketData{ValsetUpdateId: 1})
				return nil
			},
		},
	}

	for _, so := range setupOperations {
		err := so.fn(s)
		s.Require().NoError(err)
	}

	// stop the consumer chain
	err = providerKeeper.StopConsumerChain(s.providerCtx(), consumerChainID, false, true)
	s.Require().NoError(err)

	// check all states are removed and the unbonding operation released
	s.checkConsumerChainIsRemoved(consumerChainID, false, true)
}

// TODO Simon: implement OnChanCloseConfirm in IBC-GO testing to close the consumer chain's channel end
func (s *CCVTestSuite) TestStopConsumerOnChannelClosed() {
	// init the CCV channel states
	s.SetupCCVChannel()
	s.SetupTransferChannel()
	s.SendEmptyVSCPacket()

	providerKeeper := s.providerApp.GetProviderKeeper()

	// stop the consumer chain
	err := providerKeeper.StopConsumerChain(s.providerCtx(), s.consumerChain.ChainID, true, true)
	s.Require().NoError(err)

	err = s.path.EndpointA.UpdateClient()
	s.Require().NoError(err)

	// check that provider chain's channel end is closed
	s.Require().Equal(channeltypes.CLOSED, s.path.EndpointB.GetChannel().State)

	// simulate a relayer behaviour
	// err = s.path.EndpointA.OnChanCloseConfirm()
	// s.Require().NoError(err)

	// expect to panic in consumer chain's BeginBlock due to the above
	//s.consumerChain.NextBlock()

	// check that the provider's channel is removed
	// _, found := s.consumerApp.GetConsumerKeeper().GetProviderChannel(s.consumerCtx())
	// s.Require().False(found)
}

func (s *CCVTestSuite) checkConsumerChainIsRemoved(chainID string, lockUbd bool, checkChannel bool) {
	channelID := s.path.EndpointB.ChannelID
	providerKeeper := s.providerApp.GetProviderKeeper()
	providerStakingKeeper := s.providerApp.GetE2eStakingKeeper()

	if checkChannel {
		// check channel's state is closed
		s.Require().Equal(channeltypes.CLOSED, s.path.EndpointB.GetChannel().State)
	}

	// check UnbondingOps were deleted and undelegation entries aren't onHold
	if !lockUbd {
		providerKeeper.IterateOverUnbondingOpIndex(
			s.providerCtx(),
			chainID,
			func(vscID uint64, ubdIndex []uint64) bool {
				_, found := providerKeeper.GetUnbondingOpIndex(s.providerCtx(), chainID, uint64(vscID))
				s.Require().False(found)
				for _, ubdID := range ubdIndex {
					_, found = providerKeeper.GetUnbondingOp(s.providerCtx(), ubdIndex[ubdID])
					s.Require().False(found)
					ubd, _ := providerStakingKeeper.GetUnbondingDelegationByUnbondingId(s.providerCtx(), ubdIndex[ubdID])
					s.Require().Zero(ubd.Entries[ubdID].UnbondingOnHoldRefCount)
				}
				return true
			},
		)

	}

	// verify consumer chain's states are removed
	_, found := providerKeeper.GetConsumerGenesis(s.providerCtx(), chainID)
	s.Require().False(found)
	s.Require().False(providerKeeper.GetLockUnbondingOnTimeout(s.providerCtx(), chainID))
	_, found = providerKeeper.GetConsumerClientId(s.providerCtx(), chainID)
	s.Require().False(found)

	_, found = providerKeeper.GetChainToChannel(s.providerCtx(), chainID)
	s.Require().False(found)

	_, found = providerKeeper.GetChannelToChain(s.providerCtx(), channelID)
	s.Require().False(found)

	s.Require().Nil(providerKeeper.GetSlashAcks(s.providerCtx(), chainID))
	s.Require().Zero(providerKeeper.GetInitChainHeight(s.providerCtx(), chainID))
	s.Require().Nil(providerKeeper.GetPendingVSCs(s.providerCtx(), chainID))
}

// TestProviderChannelClosed checks that a consumer chain panics
// when the provider channel was established and then closed
func (suite *CCVTestSuite) TestProviderChannelClosed() {

	suite.SetupCCVChannel()
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
