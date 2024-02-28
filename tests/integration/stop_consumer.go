package integration

import (
	"cosmossdk.io/math"
	channeltypes "github.com/cosmos/ibc-go/v8/modules/core/04-channel/types"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	ccv "github.com/cosmos/interchain-security/v4/x/ccv/types"
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
		bondAmt = math.NewInt(1000000)
		// number of unbonding operations performed
		ubdOpsNum = 4
		// store new shares created
		testShares math.LegacyDec
	)

	// populate the provider chain states to setup the test using the following operations:
	// 	- setup CCV channel; establish CCV channel and set channelToChain, chainToChannel and initHeight mapping for the consumer chain ID
	// 	- delegate the total bond amount to the chose validator
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
}
