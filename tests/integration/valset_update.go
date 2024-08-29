package integration

import (
	"time"

	"cosmossdk.io/math"
	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"

	abci "github.com/cometbft/cometbft/abci/types"

	ccv "github.com/cosmos/interchain-security/v5/x/ccv/types"
)

// TestPacketRoundtrip tests a CCV packet roundtrip when tokens are bonded on the provider.
// @Long Description@
// It sets up CCV and transfer channels. Some tokens are then bonded on the provider side in order to change validator power.
// The test then relays a packet from the provider chain to the consumer chain.
// Lastly, it relays a matured packet from the consumer chain back to the provider chain.
func (s *CCVTestSuite) TestPacketRoundtrip() {
	s.SetupCCVChannel(s.path)
	s.SetupTransferChannel()

	// Bond some tokens on provider to change validator powers
	bondAmt := math.NewInt(1000000)
	delAddr := s.providerChain.SenderAccount.GetAddress()
	delegate(s, delAddr, bondAmt)

	// Send CCV packet to consumer at the end of the epoch
	s.nextEpoch()

	// Relay 1 VSC packet from provider to consumer
	relayAllCommittedPackets(s, s.providerChain, s.path, ccv.ProviderPortID, s.path.EndpointB.ChannelID, 1)

	// Increment time so that the unbonding period ends on the provider
	incrementTimeByUnbondingPeriod(s, Provider)

	// Relay 1 VSCMatured packet from consumer to provider
	relayAllCommittedPackets(s, s.consumerChain, s.path, ccv.ConsumerPortID, s.path.EndpointA.ChannelID, 1)
}

// TestQueueAndSendVSCMaturedPackets tests the behavior of EndBlock QueueVSCMaturedPackets call and its integration with SendPackets call.
// @Long Description@
// It sets up CCV channel and then creates and simulates the sending of three VSC packets
// from the provider chain to the consumer chain at different times. The first packet is sent, and its processing is validated.
// After simulating the passage of one hour, the second packet is sent and its processing is validated. Then after simulating the
// passage of 24 more hours, the third packet is sent and its processing is validated. The test then retrieves all packet maturity
// times from the consumer, and this is used to check the maturity status of the packets sent earlier.
// The test then advances the time so that the first two packets reach their unbonding period, while the third packet does not.
// Next it ensures first two packets are unbonded, their maturity times are deleted, and that VSCMatured packets are queued.
// The third packet is still in the store and has not yet been processed for unbonding.
// Finally, the test checks that the packet commitments for the processed packets are correctly reflected in the consumer chain's state.
func (suite *CCVTestSuite) TestQueueAndSendVSCMaturedPackets() {
	consumerKeeper := suite.consumerApp.GetConsumerKeeper()

	// setup CCV channel
	suite.SetupCCVChannel(suite.path)

	// send 3 packets to consumer chain at different times
	pk, err := cryptocodec.FromCmtPubKeyInterface(suite.providerChain.Vals.Validators[0].PubKey)
	suite.Require().NoError(err)
	pk1, err := cryptocodec.ToCmtProtoPublicKey(pk)
	suite.Require().NoError(err)
	pk, err = cryptocodec.FromCmtPubKeyInterface(suite.providerChain.Vals.Validators[1].PubKey)
	suite.Require().NoError(err)
	pk2, err := cryptocodec.ToCmtProtoPublicKey(pk)
	suite.Require().NoError(err)

	pd := ccv.NewValidatorSetChangePacketData(
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
	packet := suite.newPacketFromProvider(pd.GetBytes(), 1, suite.path, clienttypes.NewHeight(1, 0), 0)
	err = consumerKeeper.OnRecvVSCPacket(suite.consumerChain.GetContext(), packet, pd)
	suite.Require().Nil(err, "OnRecvVSCPacket did return non-nil error")

	// increase time
	incrementTime(suite, time.Hour)

	// update time and send second packet
	pd.ValidatorUpdates[0].Power = 15
	pd.ValsetUpdateId = 2
	packet.Data = pd.GetBytes()
	packet.Sequence = 2
	err = consumerKeeper.OnRecvVSCPacket(suite.consumerChain.GetContext(), packet, pd)
	suite.Require().Nil(err, "OnRecvVSCPacket did return non-nil error")

	// increase time
	incrementTime(suite, 24*time.Hour)

	// update time and send third packet
	pd.ValidatorUpdates[1].Power = 40
	pd.ValsetUpdateId = 3
	packet.Data = pd.GetBytes()
	packet.Sequence = 3
	err = consumerKeeper.OnRecvVSCPacket(suite.consumerChain.GetContext(), packet, pd)
	suite.Require().Nil(err, "OnRecvVSCPacket did return non-nil error")

	packetMaturities := consumerKeeper.GetAllPacketMaturityTimes(suite.consumerChain.GetContext())

	// increase time such that first two packets are unbonded but third is not.
	unbondingPeriod := consumerKeeper.GetUnbondingPeriod(suite.consumerChain.GetContext())
	// increase time
	incrementTime(suite, unbondingPeriod-time.Hour)

	// ensure first two packets are unbonded and VSCMatured packets are queued
	// unbonded time is deleted
	suite.Require().False(
		consumerKeeper.PacketMaturityTimeExists(
			suite.consumerChain.GetContext(),
			packetMaturities[0].VscId,
			packetMaturities[0].MaturityTime,
		),
		"maturity time not deleted for mature packet 1",
	)
	suite.Require().False(
		consumerKeeper.PacketMaturityTimeExists(
			suite.consumerChain.GetContext(),
			packetMaturities[1].VscId,
			packetMaturities[1].MaturityTime,
		),
		"maturity time not deleted for mature packet 2",
	)
	// ensure that third packet did not get unbonded and is still in store
	suite.Require().True(
		consumerKeeper.PacketMaturityTimeExists(
			suite.consumerChain.GetContext(),
			packetMaturities[2].VscId,
			packetMaturities[2].MaturityTime,
		),
		"maturity time for packet 3 is not after current time",
	)

	// check that the packets are committed in state
	commitments := suite.consumerApp.GetIBCKeeper().ChannelKeeper.GetAllPacketCommitmentsAtChannel(
		suite.consumerChain.GetContext(),
		ccv.ConsumerPortID,
		suite.path.EndpointA.ChannelID,
	)
	suite.Require().Equal(2, len(commitments), "did not find packet commitments")
	suite.Require().Equal(uint64(1), commitments[0].Sequence, "did not send VSCMatured packet for VSC packet 1")
	suite.Require().Equal(uint64(2), commitments[1].Sequence, "did not send VSCMatured packet for VSC packet 2")
}
