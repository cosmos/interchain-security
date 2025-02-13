package integration

import (
	channeltypes "github.com/cosmos/ibc-go/v9/modules/core/04-channel/types"

	"cosmossdk.io/math"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	"github.com/cosmos/interchain-security/v7/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/v7/x/ccv/types"
)

// TestStopConsumerChain tests the functionality of stopping a consumer chain at a higher level than unit tests.
// @Long Description@
// * Retrieve a validator from the provider chain's validators and then the delegator address.
// * Set up test operations, populating the provider chain states using the following operations:
//   - Setup CCV channels; establishes the CCV channel and sets channelToChain, chainToChannel, and initHeight mapping for the consumer chain ID.
//   - Delegate the total bond amount to the chosen validator.
//   - Undelegate the shares in four consecutive blocks evenly; create UnbondingOp and UnbondingOpIndex entries for the consumer chain ID.
//   - Set SlashAck state for the consumer chain ID.
//
// * After, the setup operations are executed, and the consumer chain is stopped.
// * Check that the state associated with the consumer chain is properly cleaned up after it is stopped.
func (s *CCVTestSuite) TestStopConsumerChain() {
	providerKeeper := s.providerApp.GetProviderKeeper()
	providerStakingKeeper := s.providerApp.GetTestStakingKeeper()

	firstBundle := s.getFirstBundle()

	// choose a validator
	tmValidator := s.providerChain.Vals.Validators[0]
	valAddr, err := sdk.ValAddressFromHex(tmValidator.Address.String())
	s.Require().NoError(err)

	validator, err := providerStakingKeeper.GetValidator(s.providerCtx(), valAddr)
	s.Require().NoError(err)

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
					_, _, err := providerStakingKeeper.Undelegate(s.providerCtx(), delAddr, valAddr, testShares.QuoInt64(int64(ubdOpsNum)))
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
				providerKeeper.SetSlashAcks(s.providerCtx(), firstBundle.ConsumerId, []string{"validator-1", "validator-2", "validator-3"})
				providerKeeper.AppendPendingVSCPackets(s.providerCtx(), firstBundle.ConsumerId, ccv.ValidatorSetChangePacketData{ValsetUpdateId: 1})
				return nil
			},
		},
	}

	for _, so := range setupOperations {
		err := so.fn(s)
		s.Require().NoError(err)
	}

	// stop the consumer chain
	providerKeeper.SetConsumerPhase(s.providerCtx(), firstBundle.ConsumerId, types.CONSUMER_PHASE_STOPPED)
	err = providerKeeper.DeleteConsumerChain(s.providerCtx(), firstBundle.ConsumerId)
	s.Require().NoError(err)

	// check all states are removed and the unbonding operation released
	s.checkConsumerChainIsRemoved(firstBundle.ConsumerId, true)
}

// TestStopConsumerOnChannelClosed tests stopping a consumer chain correctly.
// @Long Description@
// * Set up CCV channel and transfer channel, and send empty VSC packet.
// * Stop the consumer chain and verify that the provider chain's channel end is closed.
//
// TODO Simon: implement OnChanCloseConfirm in IBC-GO testing to close the consumer chain's channel end
func (s *CCVTestSuite) TestStopConsumerOnChannelClosed() {
	// init the CCV channel states
	s.SetupCCVChannel(s.path)
	s.SetupTransferChannel()
	s.SendEmptyVSCPacket()

	providerKeeper := s.providerApp.GetProviderKeeper()

	// stop the consumer chain
	providerKeeper.SetConsumerPhase(s.providerCtx(), s.getFirstBundle().ConsumerId, types.CONSUMER_PHASE_STOPPED)
	err := providerKeeper.DeleteConsumerChain(s.providerCtx(), s.getFirstBundle().ConsumerId)
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

func (s *CCVTestSuite) checkConsumerChainIsRemoved(consumerId string, checkChannel bool) {
	channelID := s.path.EndpointB.ChannelID
	providerKeeper := s.providerApp.GetProviderKeeper()

	if checkChannel {
		// check channel's state is closed
		s.Require().Equal(channeltypes.CLOSED, s.path.EndpointB.GetChannel().State)
	}

	// verify consumer chain's states are removed
	_, found := providerKeeper.GetConsumerGenesis(s.providerCtx(), consumerId)
	s.Require().False(found)
	_, found = providerKeeper.GetConsumerClientId(s.providerCtx(), consumerId)
	s.Require().False(found)

	_, found = providerKeeper.GetConsumerIdToChannelId(s.providerCtx(), consumerId)
	s.Require().False(found)

	_, found = providerKeeper.GetChannelIdToConsumerId(s.providerCtx(), channelID)
	s.Require().False(found)

	s.Require().Nil(providerKeeper.GetSlashAcks(s.providerCtx(), consumerId))
	s.Require().Zero(providerKeeper.GetInitChainHeight(s.providerCtx(), consumerId))
	s.Require().Empty(providerKeeper.GetPendingVSCPackets(s.providerCtx(), consumerId))
}
