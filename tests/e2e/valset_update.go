package e2e

import (
	"time"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	abci "github.com/tendermint/tendermint/abci/types"
)

// TestPacketRoundtrip tests a CCV packet roundtrip when tokens are bonded on provider
func (s *CCVTestSuite) TestPacketRoundtrip() {
	s.SetupCCVChannel()
	s.SetupTransferChannel()

	// Bond some tokens on provider to change validator powers
	bondAmt := sdk.NewInt(1000000)
	delAddr := s.providerChain.SenderAccount.GetAddress()
	delegate(s, delAddr, bondAmt)

	// Send CCV packet to consumer
	s.providerChain.NextBlock()

	// Relay 1 VSC packet from provider to consumer
	relayAllCommittedPackets(s, s.providerChain, s.path, ccv.ProviderPortID, s.path.EndpointB.ChannelID, 1)

	// Increment time so that the unbonding period ends on the provider
	incrementTimeByUnbondingPeriod(s, Provider)

	// Relay 1 VSCMatured packet from consumer to provider
	relayAllCommittedPackets(s, s.consumerChain, s.path, ccv.ConsumerPortID, s.path.EndpointA.ChannelID, 1)
}

// TestSendVSCMaturedPackets tests the behavior of SendVSCMaturedPackets and related state checks
func (suite *CCVTestSuite) TestSendVSCMaturedPackets() {

	consumerKeeper := suite.consumerApp.GetConsumerKeeper()

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
	packet := channeltypes.NewPacket(pd.GetBytes(), 1, ccv.ProviderPortID, suite.path.EndpointB.ChannelID, ccv.ConsumerPortID, suite.path.EndpointA.ChannelID,
		clienttypes.NewHeight(1, 0), 0)
	ack := consumerKeeper.OnRecvVSCPacket(suite.consumerChain.GetContext(), packet, pd)
	suite.Require().NotNil(ack, "OnRecvVSCPacket did not return ack")
	suite.Require().True(ack.Success(), "OnRecvVSCPacket did not return a Success Acknowledgment")

	// increase time
	incrementTimeBy(suite, time.Hour)

	// update time and send second packet
	pd.ValidatorUpdates[0].Power = 15
	pd.ValsetUpdateId = 2
	packet.Data = pd.GetBytes()
	packet.Sequence = 2
	ack = consumerKeeper.OnRecvVSCPacket(suite.consumerChain.GetContext(), packet, pd)
	suite.Require().NotNil(ack, "OnRecvVSCPacket did not return ack")
	suite.Require().True(ack.Success(), "OnRecvVSCPacket did not return a Success Acknowledgment")

	// increase time
	incrementTimeBy(suite, 24*time.Hour)

	// update time and send third packet
	pd.ValidatorUpdates[1].Power = 40
	pd.ValsetUpdateId = 3
	packet.Data = pd.GetBytes()
	packet.Sequence = 3
	ack = consumerKeeper.OnRecvVSCPacket(suite.consumerChain.GetContext(), packet, pd)
	suite.Require().NotNil(ack, "OnRecvVSCPacket did not return ack")
	suite.Require().True(ack.Success(), "OnRecvVSCPacket did not return a Success Acknowledgment")

	// increase time such that first two packets are unbonded but third is not.
	unbondingPeriod := consumerKeeper.GetUnbondingPeriod(suite.consumerChain.GetContext())
	// increase time
	incrementTimeBy(suite, unbondingPeriod-time.Hour)

	err = consumerKeeper.SendVSCMaturedPackets(suite.consumerChain.GetContext())
	suite.Require().NoError(err)

	// ensure first two packets are unbonded and VSCMatured packets are sent
	// unbonded time is deleted
	time1 := consumerKeeper.GetPacketMaturityTime(suite.consumerChain.GetContext(), 1)
	time2 := consumerKeeper.GetPacketMaturityTime(suite.consumerChain.GetContext(), 2)
	suite.Require().Equal(uint64(0), time1, "maturity time not deleted for mature packet 1")
	suite.Require().Equal(uint64(0), time2, "maturity time not deleted for mature packet 2")
	// ensure that third packet did not get unbonded and is still in store
	time3 := consumerKeeper.GetPacketMaturityTime(suite.consumerChain.GetContext(), 3)
	suite.Require().True(time3 > uint64(suite.consumerChain.GetContext().BlockTime().UnixNano()), "maturity time for packet 3 is not after current time")

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
