package e2e_test

import (
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	appProvider "github.com/cosmos/interchain-security/app/provider"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	abci "github.com/tendermint/tendermint/abci/types"
)

func (s *ProviderTestSuite) TestStopConsumerChain() {

	// default consumer chain ID
	consumerChainID := s.consumerChain.ChainID

	// choose a validator
	tmValidator := s.providerChain.Vals.Validators[0]
	valAddr, err := sdk.ValAddressFromHex(tmValidator.Address.String())
	s.Require().NoError(err)

	validator, found := s.providerChain.App.(*appProvider.App).StakingKeeper.GetValidator(s.providerCtx(), valAddr)
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
		fn func(suite *ProviderTestSuite) error
	}{
		{
			func(suite *ProviderTestSuite) error {
				suite.SetupCCVChannel()
				return nil
			},
		},
		{
			func(suite *ProviderTestSuite) error {
				testShares, err = s.providerChain.App.(*appProvider.App).StakingKeeper.Delegate(s.providerCtx(), delAddr, bondAmt, stakingtypes.Unbonded, stakingtypes.Validator(validator), true)
				return err
			},
		},
		{
			func(suite *ProviderTestSuite) error {
				for i := 0; i < ubdOpsNum; i++ {
					// undelegate one quarter of the shares
					_, err := s.providerChain.App.(*appProvider.App).StakingKeeper.Undelegate(s.providerCtx(), delAddr, valAddr, testShares.QuoInt64(int64(ubdOpsNum)))
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
			func(suite *ProviderTestSuite) error {
				s.providerChain.App.(*appProvider.App).ProviderKeeper.SetSlashAcks(s.providerCtx(), consumerChainID, []string{"validator-1", "validator-2", "validator-3"})
				s.providerChain.App.(*appProvider.App).ProviderKeeper.SetLockUnbondingOnTimeout(s.providerCtx(), consumerChainID)
				return nil
			},
		},
	}

	for _, so := range setupOperations {
		err := so.fn(s)
		s.Require().NoError(err)
	}

	// stop the consumer chain
	err = s.providerChain.App.(*appProvider.App).ProviderKeeper.StopConsumerChain(s.providerCtx(), consumerChainID, false, true)
	s.Require().NoError(err)

	// check all states are removed and the unbonding operation released
	s.checkConsumerChainIsRemoved(consumerChainID, false)
}

func (s *ProviderTestSuite) TestConsumerRemovalProposal() {
	var (
		ctx      sdk.Context
		proposal *providertypes.ConsumerRemovalProposal
		ok       bool
	)

	chainID := s.consumerChain.ChainID

	testCases := []struct {
		name        string
		malleate    func(*ProviderTestSuite)
		expPass     bool
		stopReached bool
	}{
		{
			"valid consumer removal proposal: stop time reached", func(suite *ProviderTestSuite) {

				// ctx blocktime is after proposal's stop time
				ctx = s.providerCtx().WithBlockTime(time.Now().Add(time.Hour))
				content, err := providertypes.NewConsumerRemovalProposal("title", "description", chainID, time.Now())
				s.Require().NoError(err)
				proposal, ok = content.(*providertypes.ConsumerRemovalProposal)
				s.Require().True(ok)
			}, true, true,
		},
		{
			"valid proposal: stop time has not yet been reached", func(suite *ProviderTestSuite) {

				// ctx blocktime is before proposal's stop time
				ctx = s.providerCtx().WithBlockTime(time.Now())
				content, err := providertypes.NewConsumerRemovalProposal("title", "description", chainID, time.Now().Add(time.Hour))
				s.Require().NoError(err)
				proposal, ok = content.(*providertypes.ConsumerRemovalProposal)
				s.Require().True(ok)
			}, true, false,
		},
		{
			"valid proposal: fail due to an invalid unbonding index", func(suite *ProviderTestSuite) {

				// ctx blocktime is after proposal's stop time
				ctx = s.providerCtx().WithBlockTime(time.Now().Add(time.Hour))

				// set invalid unbonding op index
				s.providerChain.App.(*appProvider.App).ProviderKeeper.SetUnbondingOpIndex(ctx, chainID, 0, []uint64{0})

				content, err := providertypes.NewConsumerRemovalProposal("title", "description", chainID, time.Now())
				s.Require().NoError(err)
				proposal, ok = content.(*providertypes.ConsumerRemovalProposal)
				s.Require().True(ok)
			}, false, true,
		},
	}

	for _, tc := range testCases {
		tc := tc

		s.Run(tc.name, func() {
			s.SetupTest()
			s.SetupCCVChannel()

			tc.malleate(s)

			err := s.providerChain.App.(*appProvider.App).ProviderKeeper.HandleConsumerRemovalProposal(ctx, proposal)
			if tc.expPass {
				s.Require().NoError(err, "error returned on valid case")
				if tc.stopReached {
					// check that the pending consumer removal proposal is deleted
					found := s.providerChain.App.(*appProvider.App).ProviderKeeper.GetPendingConsumerRemovalProp(ctx, chainID, proposal.StopTime)
					s.Require().False(found, "pending consumer removal proposal wasn't deleted")

					// check that the consumer chain is removed
					s.checkConsumerChainIsRemoved(chainID, false)

				} else {
					found := s.providerChain.App.(*appProvider.App).ProviderKeeper.GetPendingConsumerRemovalProp(ctx, chainID, proposal.StopTime)
					s.Require().True(found, "pending stop consumer was not found for chain ID %s", chainID)

					// check that the consumer chain client exists
					_, found = s.providerChain.App.(*appProvider.App).ProviderKeeper.GetConsumerClientId(s.providerCtx(), chainID)
					s.Require().True(found)

					// check that the chainToChannel and channelToChain exist for the consumer chain ID
					_, found = s.providerChain.App.(*appProvider.App).ProviderKeeper.GetChainToChannel(s.providerCtx(), chainID)
					s.Require().True(found)

					_, found = s.providerChain.App.(*appProvider.App).ProviderKeeper.GetChannelToChain(s.providerCtx(), s.path.EndpointB.ChannelID)
					s.Require().True(found)

					// check that channel is in OPEN state
					s.Require().Equal(channeltypes.OPEN, s.path.EndpointB.GetChannel().State)
				}
			} else {
				s.Require().Error(err, "did not return error on invalid case")
			}
		})
	}
}

// TODO Simon: implement OnChanCloseConfirm in IBC-GO testing to close the consumer chain's channel end
func (s *ProviderTestSuite) TestStopConsumerOnChannelClosed() {
	// init the CCV channel states
	s.SetupCCVChannel()
	s.SendEmptyVSCPacket()

	// stop the consumer chain
	err := s.providerChain.App.(*appProvider.App).ProviderKeeper.StopConsumerChain(s.providerCtx(), s.consumerChain.ChainID, true, true)
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
	// _, found := s.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetProviderChannel(s.consumerCtx())
	// s.Require().False(found)
}

func (s *ProviderTestSuite) checkConsumerChainIsRemoved(chainID string, lockUbd bool) {
	channelID := s.path.EndpointB.ChannelID
	providerKeeper := s.providerChain.App.(*appProvider.App).ProviderKeeper

	// check channel's state is closed
	s.Require().Equal(channeltypes.CLOSED, s.path.EndpointB.GetChannel().State)

	// check UnbondingOps were deleted and undelegation entries aren't onHold
	if !lockUbd {
		s.providerChain.App.(*appProvider.App).ProviderKeeper.IterateOverUnbondingOpIndex(
			s.providerCtx(),
			chainID,
			func(vscID uint64, ubdIndex []uint64) bool {
				_, found := providerKeeper.GetUnbondingOpIndex(s.providerCtx(), chainID, uint64(vscID))
				s.Require().False(found)
				for _, ubdID := range ubdIndex {
					_, found = providerKeeper.GetUnbondingOp(s.providerCtx(), ubdIndex[ubdID])
					s.Require().False(found)
					ubd, _ := s.providerChain.App.(*appProvider.App).StakingKeeper.GetUnbondingDelegationByUnbondingId(s.providerCtx(), ubdIndex[ubdID])
					s.Require().Zero(ubd.Entries[ubdID].UnbondingOnHoldRefCount)
				}
				return true
			},
		)

	}

	// verify consumer chain's states are removed
	s.Require().False(providerKeeper.GetLockUnbondingOnTimeout(s.providerCtx(), chainID))
	_, found := providerKeeper.GetConsumerClientId(s.providerCtx(), chainID)
	s.Require().False(found)

	_, found = providerKeeper.GetChainToChannel(s.providerCtx(), chainID)
	s.Require().False(found)

	_, found = providerKeeper.GetChannelToChain(s.providerCtx(), channelID)
	s.Require().False(found)

	s.Require().Nil(providerKeeper.GetSlashAcks(s.providerCtx(), chainID))
	s.Require().Zero(providerKeeper.GetInitChainHeight(s.providerCtx(), chainID))
	// TODO Simon: check that pendingVSCPacket are emptied - once
	// https://github.com/cosmos/interchain-security/issues/27 is implemented
}

// TODO Simon: duplicated from consumer/keeper_test.go; figure out how it can be refactored
// SendEmptyVSCPacket sends a VSC packet without any changes
// to ensure that the CCV channel gets established
func (s *ProviderTestSuite) SendEmptyVSCPacket() {
	providerKeeper := s.providerChain.App.(*appProvider.App).ProviderKeeper

	oldBlockTime := s.providerChain.GetContext().BlockTime()
	timeout := uint64(ccv.GetTimeoutTimestamp(oldBlockTime).UnixNano())

	valUpdateID := providerKeeper.GetValidatorSetUpdateId(s.providerChain.GetContext())

	pd := ccv.NewValidatorSetChangePacketData(
		[]abci.ValidatorUpdate{},
		valUpdateID,
		nil,
	)

	seq, ok := s.providerChain.App.(*appProvider.App).GetIBCKeeper().ChannelKeeper.GetNextSequenceSend(
		s.providerChain.GetContext(), ccv.ProviderPortID, s.path.EndpointB.ChannelID)
	s.Require().True(ok)

	packet := channeltypes.NewPacket(pd.GetBytes(), seq, ccv.ProviderPortID, s.path.EndpointB.ChannelID,
		ccv.ConsumerPortID, s.path.EndpointA.ChannelID, clienttypes.Height{}, timeout)

	err := s.path.EndpointB.SendPacket(packet)
	s.Require().NoError(err)
	err = s.path.EndpointA.RecvPacket(packet)
	s.Require().NoError(err)
}
