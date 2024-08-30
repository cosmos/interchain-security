package integration

import (
	"fmt"

	transfertypes "github.com/cosmos/ibc-go/v8/modules/apps/transfer/types"
	channeltypes "github.com/cosmos/ibc-go/v8/modules/core/04-channel/types"
)

// TestRecycleTransferChannel tests that an existing transfer channel can be reused when transitioning from
// a standalone to a consumer chain.
// @Long Description@
// The test case:
// * sets up a provider chain and a standalone chain
// * creates a connection between the two chains
// * creates a transfer channel between the two chains
// * transitions the standalone chain to a consumer chain
// * confirms that no extra transfer channel is created, thus only one transfer channel and one CCV channel exist.
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

// TestFoo tests testing-docs test
// @Long Description@
// It will be deleted
func (suite *CCVTestSuite) TestFoo() {

	fmt.Println("Foo test")
}
