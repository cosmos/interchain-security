package keeper_test

import (
	"sort"
	"time"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	"github.com/cosmos/interchain-security/x/ccv/types"
	abci "github.com/tendermint/tendermint/abci/types"
	"github.com/tendermint/tendermint/libs/bytes"
)

func (suite *KeeperTestSuite) TestOnRecvPacket() {
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
		ack := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.OnRecvPacket(suite.ctx, tc.packet, tc.newChanges)

		if tc.expErrorAck {
			suite.Require().NotNil(ack, "invalid test case: %s did not return ack", tc.name)
			suite.Require().False(ack.Success(), "invalid test case: %s did not return an Error Acknowledgment")
		} else {
			suite.Require().Nil(ack, "successful packet must send ack asynchronously. case: %s", tc.name)
			providerChannel, ok := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetProviderChannel(suite.ctx)
			suite.Require().True(ok)
			suite.Require().Equal(tc.packet.DestinationChannel, providerChannel,
				"provider channel is not destination channel on successful receive for valid test case: %s", tc.name)

			// Check that pending changes are accumulated and stored correctly
			actualPendingChanges, ok := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetPendingChanges(suite.ctx)
			suite.Require().True(ok)
			// Sort to avoid dumb inequalities
			sort.SliceStable(actualPendingChanges.ValidatorUpdates, func(i, j int) bool {
				return actualPendingChanges.ValidatorUpdates[i].PubKey.Compare(actualPendingChanges.ValidatorUpdates[j].PubKey) == -1
			})
			sort.SliceStable(tc.expectedPendingChanges.ValidatorUpdates, func(i, j int) bool {
				return tc.expectedPendingChanges.ValidatorUpdates[i].PubKey.Compare(tc.expectedPendingChanges.ValidatorUpdates[j].PubKey) == -1
			})
			suite.Require().Equal(tc.expectedPendingChanges, *actualPendingChanges, "pending changes not equal to expected changes after successful packet receive. case: %s", tc.name)

			unbondingPeriod, found := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetUnbondingTime(suite.ctx)
			suite.Require().True(found)
			expectedTime := uint64(suite.ctx.BlockTime().Add(unbondingPeriod).UnixNano())
			maturityTime := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetPacketMaturityTime(suite.ctx, tc.newChanges.ValsetUpdateId)
			suite.Require().Equal(expectedTime, maturityTime, "packet maturity time has unexpected value for case: %s", tc.name)
		}
	}
}

func (suite *KeeperTestSuite) TestUnbondMaturePackets() {
	// setup CCV channel
	suite.SetupCCVChannel()

	// send 3 packets to consumer chain at different times
	pk1, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
	suite.Require().NoError(err)
	pk2, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
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

	origTime := suite.ctx.BlockTime()

	// send first packet
	packet := channeltypes.NewPacket(pd.GetBytes(), 1, providertypes.PortID, suite.path.EndpointB.ChannelID, consumertypes.PortID, suite.path.EndpointA.ChannelID,
		clienttypes.NewHeight(1, 0), 0)
	ack := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.OnRecvPacket(suite.ctx, packet, pd)
	suite.Require().Nil(ack)

	// update time and send second packet
	suite.ctx = suite.ctx.WithBlockTime(suite.ctx.BlockTime().Add(time.Hour))
	pd.ValidatorUpdates[0].Power = 15
	pd.ValsetUpdateId = 2
	packet.Data = pd.GetBytes()
	packet.Sequence = 2
	ack = suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.OnRecvPacket(suite.ctx, packet, pd)
	suite.Require().Nil(ack)

	// update time and send third packet
	suite.ctx = suite.ctx.WithBlockTime(suite.ctx.BlockTime().Add(24 * time.Hour))
	pd.ValidatorUpdates[1].Power = 40
	pd.ValsetUpdateId = 3
	packet.Data = pd.GetBytes()
	packet.Sequence = 3
	ack = suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.OnRecvPacket(suite.ctx, packet, pd)
	suite.Require().Nil(ack)

	// move ctx time forward such that first two packets are unbonded but third is not.
	unbondingPeriod, found := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetUnbondingTime(suite.ctx)
	suite.Require().True(found)
	suite.ctx = suite.ctx.WithBlockTime(origTime.Add(unbondingPeriod).Add(3 * time.Hour))

	suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.UnbondMaturePackets(suite.ctx)

	// ensure first two packets are unbonded and acknowledgement is written
	// unbonded time is deleted
	time1 := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetPacketMaturityTime(suite.ctx, 1)
	time2 := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetPacketMaturityTime(suite.ctx, 2)
	suite.Require().Equal(uint64(0), time1, "maturity time not deleted for mature packet 1")
	suite.Require().Equal(uint64(0), time2, "maturity time not deleted for mature packet 2")

	expectedWriteAckBytes := channeltypes.CommitAcknowledgement(channeltypes.NewResultAcknowledgement([]byte{byte(1)}).Acknowledgement())

	// successful acknowledgements are written
	ackBytes1, ok := suite.consumerChain.App.GetIBCKeeper().ChannelKeeper.GetPacketAcknowledgement(suite.ctx, consumertypes.PortID, suite.path.EndpointA.ChannelID, 1)
	suite.Require().True(ok)
	suite.Require().Equal(expectedWriteAckBytes, ackBytes1, "did not write successful ack for mature packet 1")
	ackBytes2, ok := suite.consumerChain.App.GetIBCKeeper().ChannelKeeper.GetPacketAcknowledgement(suite.ctx, consumertypes.PortID, suite.path.EndpointA.ChannelID, 2)
	suite.Require().True(ok)
	suite.Require().Equal(expectedWriteAckBytes, ackBytes2, "did not write successful ack for mature packet 1")

	// ensure that third packet did not get ack written and is still in store
	time3 := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetPacketMaturityTime(suite.ctx, 3)
	suite.Require().True(time3 > uint64(suite.ctx.BlockTime().UnixNano()), "maturity time for packet 3 is not after current time")

	// ensure acknowledgement has not been written for unbonding packet
	ackBytes3, ok := suite.consumerChain.App.GetIBCKeeper().ChannelKeeper.GetPacketAcknowledgement(suite.ctx, consumertypes.PortID, suite.path.EndpointA.ChannelID, 3)
	suite.Require().False(ok)
	suite.Require().Nil(ackBytes3, "acknowledgement written for unbonding packet 3")
}

func (suite *KeeperTestSuite) TestOnAcknowledgement() {
	packetData := types.NewSlashPacketData(
		abci.Validator{Address: bytes.HexBytes{}, Power: int64(1)}, uint64(1), stakingtypes.Downtime,
	)

	packet := channeltypes.NewPacket(packetData.GetBytes(), 1, providertypes.PortID, suite.path.EndpointB.ChannelID,
		consumertypes.PortID, suite.path.EndpointA.ChannelID, clienttypes.Height{}, uint64(time.Now().Add(60*time.Second).UnixNano()))
	ack := channeltypes.NewResultAcknowledgement([]byte{1})

	// expect no error
	err := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.OnAcknowledgementPacket(suite.ctx, packet, ack)
	suite.Nil(err)

	// expect an error
	ack = channeltypes.NewErrorAcknowledgement("error")

	err = suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.OnAcknowledgementPacket(suite.ctx, packet, ack)
	suite.NotNil(err)
}
