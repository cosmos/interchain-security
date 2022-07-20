package keeper_test

import (
	"sort"
	"time"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	"github.com/cosmos/interchain-security/testutil/simapp"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	"github.com/cosmos/interchain-security/x/ccv/types"
	"github.com/cosmos/interchain-security/x/ccv/utils"
	abci "github.com/tendermint/tendermint/abci/types"
	"github.com/tendermint/tendermint/libs/bytes"
)

func (suite *KeeperTestSuite) TestOnRecvVSCPacket() {
	// setup CCV channel
	suite.SetupCCVChannel()

	pk1, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
	suite.Require().NoError(err)
	pk2, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
	suite.Require().NoError(err)
	pk3, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
	suite.Require().NoError(err)

	changes1 := []abci.ValidatorUpdate{
		{
			PubKey: pk1,
			Power:  30,
		},
		{
			PubKey: pk2,
			Power:  20,
		},
	}

	changes2 := []abci.ValidatorUpdate{
		{
			PubKey: pk2,
			Power:  40,
		},
		{
			PubKey: pk3,
			Power:  10,
		},
	}

	pd := types.NewValidatorSetChangePacketData(
		changes1,
		1,
		nil,
	)

	pd2 := types.NewValidatorSetChangePacketData(
		changes2,
		2,
		nil,
	)

	testCases := []struct {
		name                   string
		packet                 channeltypes.Packet
		newChanges             types.ValidatorSetChangePacketData
		expectedPendingChanges types.ValidatorSetChangePacketData
		expErrorAck            bool
	}{
		{
			"success on first packet",
			channeltypes.NewPacket(pd.GetBytes(), 1, providertypes.PortID, suite.path.EndpointB.ChannelID, consumertypes.PortID, suite.path.EndpointA.ChannelID,
				clienttypes.NewHeight(1, 0), 0),
			types.ValidatorSetChangePacketData{ValidatorUpdates: changes1},
			types.ValidatorSetChangePacketData{ValidatorUpdates: changes1},
			false,
		},
		{
			"success on subsequent packet",
			channeltypes.NewPacket(pd.GetBytes(), 2, providertypes.PortID, suite.path.EndpointB.ChannelID, consumertypes.PortID, suite.path.EndpointA.ChannelID,
				clienttypes.NewHeight(1, 0), 0),
			types.ValidatorSetChangePacketData{ValidatorUpdates: changes1},
			types.ValidatorSetChangePacketData{ValidatorUpdates: changes1},
			false,
		},
		{
			"success on packet with more changes",
			channeltypes.NewPacket(pd2.GetBytes(), 3, providertypes.PortID, suite.path.EndpointB.ChannelID, consumertypes.PortID, suite.path.EndpointA.ChannelID,
				clienttypes.NewHeight(1, 0), 0),
			types.ValidatorSetChangePacketData{ValidatorUpdates: changes2},
			types.ValidatorSetChangePacketData{ValidatorUpdates: []abci.ValidatorUpdate{
				{
					PubKey: pk1,
					Power:  30,
				},
				{
					PubKey: pk2,
					Power:  40,
				},
				{
					PubKey: pk3,
					Power:  10,
				},
			}},
			false,
		},
		{
			"invalid packet: different destination channel than provider channel",
			channeltypes.NewPacket(pd.GetBytes(), 1, providertypes.PortID, suite.path.EndpointB.ChannelID, consumertypes.PortID, "InvalidChannel",
				clienttypes.NewHeight(1, 0), 0),
			types.ValidatorSetChangePacketData{ValidatorUpdates: []abci.ValidatorUpdate{}},
			types.ValidatorSetChangePacketData{ValidatorUpdates: []abci.ValidatorUpdate{}},
			true,
		},
	}

	for _, tc := range testCases {
		ack := simapp.GetConsumerKeeper(suite.consumerChain.App).OnRecvVSCPacket(suite.ctx, tc.packet, tc.newChanges)
		suite.Require().NotNil(ack, "invalid test case: %s did not return ack", tc.name)

		if tc.expErrorAck {
			suite.Require().False(ack.Success(), "invalid test case: %s did not return an Error Acknowledgment", tc.name)
		} else {
			suite.Require().True(ack.Success(), "invalid test case: %s did not return a Success Acknowledgment", tc.name)
			providerChannel, ok := simapp.GetConsumerKeeper(suite.consumerChain.App).GetProviderChannel(suite.ctx)
			suite.Require().True(ok)
			suite.Require().Equal(tc.packet.DestinationChannel, providerChannel,
				"provider channel is not destination channel on successful receive for valid test case: %s", tc.name)

			// Check that pending changes are accumulated and stored correctly
			actualPendingChanges, ok := simapp.GetConsumerKeeper(suite.consumerChain.App).GetPendingChanges(suite.ctx)
			suite.Require().True(ok)
			// Sort to avoid dumb inequalities
			sort.SliceStable(actualPendingChanges.ValidatorUpdates, func(i, j int) bool {
				return actualPendingChanges.ValidatorUpdates[i].PubKey.Compare(actualPendingChanges.ValidatorUpdates[j].PubKey) == -1
			})
			sort.SliceStable(tc.expectedPendingChanges.ValidatorUpdates, func(i, j int) bool {
				return tc.expectedPendingChanges.ValidatorUpdates[i].PubKey.Compare(tc.expectedPendingChanges.ValidatorUpdates[j].PubKey) == -1
			})
			suite.Require().Equal(tc.expectedPendingChanges, *actualPendingChanges, "pending changes not equal to expected changes after successful packet receive. case: %s", tc.name)

			unbondingPeriod, found := simapp.GetConsumerKeeper(suite.consumerChain.App).GetUnbondingTime(suite.ctx)
			suite.Require().True(found)
			expectedTime := uint64(suite.ctx.BlockTime().Add(unbondingPeriod).UnixNano())
			maturityTime := simapp.GetConsumerKeeper(suite.consumerChain.App).GetPacketMaturityTime(suite.ctx, tc.newChanges.ValsetUpdateId)
			suite.Require().Equal(expectedTime, maturityTime, "packet maturity time has unexpected value for case: %s", tc.name)
		}
	}
}

func (suite *KeeperTestSuite) TestUnbondMaturePackets() {
	// setup CCV channel
	suite.SetupCCVChannel()

	// send 3 packets to consumer chain at different times
	pk, err := cryptocodec.FromTmPubKeyInterface(suite.providerChain.Vals.Validators[0].PubKey)
	suite.Require().NoError(err)
	pk1, err := cryptocodec.ToTmProtoPublicKey(pk)
	suite.Require().NoError(err)
	pk, err = cryptocodec.FromTmPubKeyInterface(suite.providerChain.Vals.Validators[1].PubKey)
	suite.Require().NoError(err)
	pk2, err := cryptocodec.ToTmProtoPublicKey(pk)
	suite.Require().NoError(err)

	pd := types.NewValidatorSetChangePacketData(
		[]abci.ValidatorUpdate{
			{
				PubKey: pk1,
				Power:  30,
			},
			{
				PubKey: pk2,
				Power:  20,
			},
		},
		1,
		nil,
	)

	// send first packet
	packet := channeltypes.NewPacket(pd.GetBytes(), 1, providertypes.PortID, suite.path.EndpointB.ChannelID, consumertypes.PortID, suite.path.EndpointA.ChannelID,
		clienttypes.NewHeight(1, 0), 0)
	ack := simapp.GetConsumerKeeper(suite.consumerChain.App).OnRecvVSCPacket(suite.consumerChain.GetContext(), packet, pd)
	suite.Require().NotNil(ack, "OnRecvVSCPacket did not return ack")
	suite.Require().True(ack.Success(), "OnRecvVSCPacket did not return a Success Acknowledgment")

	// increase time
	incrementTimeBy(suite, time.Hour)

	// update time and send second packet
	pd.ValidatorUpdates[0].Power = 15
	pd.ValsetUpdateId = 2
	packet.Data = pd.GetBytes()
	packet.Sequence = 2
	ack = simapp.GetConsumerKeeper(suite.consumerChain.App).OnRecvVSCPacket(suite.consumerChain.GetContext(), packet, pd)
	suite.Require().NotNil(ack, "OnRecvVSCPacket did not return ack")
	suite.Require().True(ack.Success(), "OnRecvVSCPacket did not return a Success Acknowledgment")

	// increase time
	incrementTimeBy(suite, 24*time.Hour)

	// update time and send third packet
	pd.ValidatorUpdates[1].Power = 40
	pd.ValsetUpdateId = 3
	packet.Data = pd.GetBytes()
	packet.Sequence = 3
	ack = simapp.GetConsumerKeeper(suite.consumerChain.App).OnRecvVSCPacket(suite.consumerChain.GetContext(), packet, pd)
	suite.Require().NotNil(ack, "OnRecvVSCPacket did not return ack")
	suite.Require().True(ack.Success(), "OnRecvVSCPacket did not return a Success Acknowledgment")

	// increase time such that first two packets are unbonded but third is not.
	unbondingPeriod, found := simapp.GetConsumerKeeper(suite.consumerChain.App).GetUnbondingTime(suite.consumerChain.GetContext())
	suite.Require().True(found)
	// increase time
	incrementTimeBy(suite, unbondingPeriod-time.Hour)

	err = simapp.GetConsumerKeeper(suite.consumerChain.App).UnbondMaturePackets(suite.consumerChain.GetContext())
	suite.Require().NoError(err)

	// ensure first two packets are unbonded and VSCMatured packets are sent
	// unbonded time is deleted
	time1 := simapp.GetConsumerKeeper(suite.consumerChain.App).GetPacketMaturityTime(suite.consumerChain.GetContext(), 1)
	time2 := simapp.GetConsumerKeeper(suite.consumerChain.App).GetPacketMaturityTime(suite.consumerChain.GetContext(), 2)
	suite.Require().Equal(uint64(0), time1, "maturity time not deleted for mature packet 1")
	suite.Require().Equal(uint64(0), time2, "maturity time not deleted for mature packet 2")
	// ensure that third packet did not get unbonded and is still in store
	time3 := simapp.GetConsumerKeeper(suite.consumerChain.App).GetPacketMaturityTime(suite.consumerChain.GetContext(), 3)
	suite.Require().True(time3 > uint64(suite.consumerChain.GetContext().BlockTime().UnixNano()), "maturity time for packet 3 is not after current time")

	// check that the packets are committed in state
	commitments := suite.consumerChain.App.GetIBCKeeper().ChannelKeeper.GetAllPacketCommitmentsAtChannel(
		suite.consumerChain.GetContext(),
		consumertypes.PortID,
		suite.path.EndpointA.ChannelID,
	)
	suite.Require().Equal(2, len(commitments), "did not find packet commitments")
	suite.Require().Equal(uint64(1), commitments[0].Sequence, "did not send VSCMatured packet for VSC packet 1")
	suite.Require().Equal(uint64(2), commitments[1].Sequence, "did not send VSCMatured packet for VSC packet 2")
}

// incrementTimeByUnbondingPeriod increments the overall time by jumpPeriod
func incrementTimeBy(s *KeeperTestSuite, jumpPeriod time.Duration) {
	// Get unboding period from staking keeper
	consumerUnbondingPeriod, found := simapp.GetConsumerKeeper(s.consumerChain.App).GetUnbondingTime(s.consumerChain.GetContext())
	s.Require().True(found)
	split := 1
	if jumpPeriod > consumerUnbondingPeriod/utils.TrustingPeriodFraction {
		// Make sure the clients do not expire
		split = 4
		jumpPeriod = jumpPeriod / 4
	}
	for i := 0; i < split; i++ {
		s.coordinator.IncrementTimeBy(jumpPeriod)
		// Update the provider client on the consumer
		err := s.path.EndpointA.UpdateClient()
		s.Require().NoError(err)
		// Update the consumer client on the provider
		err = s.path.EndpointB.UpdateClient()
		s.Require().NoError(err)
	}
}

func (suite *KeeperTestSuite) TestOnAcknowledgement() {
	packetData := types.NewSlashPacketData(
		abci.Validator{Address: bytes.HexBytes{}, Power: int64(1)}, uint64(1), stakingtypes.Downtime,
	)

	packet := channeltypes.NewPacket(packetData.GetBytes(), 1, providertypes.PortID, suite.path.EndpointB.ChannelID,
		consumertypes.PortID, suite.path.EndpointA.ChannelID, clienttypes.Height{}, uint64(time.Now().Add(60*time.Second).UnixNano()))
	ack := channeltypes.NewResultAcknowledgement([]byte{1})

	// expect no error
	err := simapp.GetConsumerKeeper(suite.consumerChain.App).OnAcknowledgementPacket(suite.ctx, packet, ack)
	suite.Nil(err)

	// expect an error
	ack = channeltypes.NewErrorAcknowledgement("error")

	err = simapp.GetConsumerKeeper(suite.consumerChain.App).OnAcknowledgementPacket(suite.ctx, packet, ack)
	suite.NotNil(err)
}
