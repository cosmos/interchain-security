package integration

import (
	transfertypes "github.com/cosmos/ibc-go/v8/modules/apps/transfer/types"
	channeltypes "github.com/cosmos/ibc-go/v8/modules/core/04-channel/types"
)

func (suite *CCVTestSuite) TestRecycleTransferChannel() {
	consumerKeeper := suite.consumerApp.GetConsumerKeeper()

	// Only create a connection between consumer and provider
	suite.coordinator.CreateConnections(suite.path)

	// Confirm transfer channel has not been persisted
	transChan := consumerKeeper.GetDistributionTransmissionChannel(suite.consumerCtx())
	suite.Require().Empty(transChan)

	// Create transfer channel manually
	distrTransferMsg := channeltypes.NewMsgChannelOpenInit(
		transfertypes.PortID,
		transfertypes.Version,
		channeltypes.UNORDERED,
		[]string{suite.path.EndpointA.ConnectionID},
		transfertypes.PortID,
		"", // signer unused
	)
	resp, err := consumerKeeper.ChannelOpenInit(suite.consumerCtx(), distrTransferMsg)
	suite.Require().NoError(err)

	// Confirm transfer channel still not persisted
	transChan = consumerKeeper.GetDistributionTransmissionChannel(suite.consumerCtx())
	suite.Require().Empty(transChan)

	// Setup state s.t. the consumer keeper emulates a consumer that was previously standalone
	consumerKeeper.MarkAsPrevStandaloneChain(suite.consumerCtx())
	suite.Require().True(consumerKeeper.IsPrevStandaloneChain(suite.consumerCtx()))
	suite.consumerApp.GetConsumerKeeper().SetDistributionTransmissionChannel(suite.consumerCtx(), resp.ChannelId)

	// Now finish setting up CCV channel
	suite.ExecuteCCVChannelHandshake(suite.path)

	// Confirm transfer channel is now persisted with expected channel id from open init response
	transChan = consumerKeeper.GetDistributionTransmissionChannel(suite.consumerCtx())
	suite.Require().Equal(resp.ChannelId, transChan)

	// Confirm channel exists
	found := consumerKeeper.TransferChannelExists(suite.consumerCtx(), transChan)
	suite.Require().True(found)

	// Sanity check, only two channels should exist, one transfer and one ccv
	channels := suite.consumerApp.GetIBCKeeper().ChannelKeeper.GetAllChannels(suite.consumerCtx())
	suite.Require().Len(channels, 2)
}
