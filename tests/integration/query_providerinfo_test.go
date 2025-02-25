package integration

import "strings"

// TestQueryProviderInfo tests the results of GetProviderInfo method.
// @Long Description@
// * Set up a CCV channel and send an empty VSC packet.
// * Verify that the result of GetProviderInfo method is correct and it
// provides expected information about the blockchain provider and consumer.
func (s *CCVTestSuite) TestQueryProviderInfo() {
	s.SetupCCVChannel(s.path)
	s.SendEmptyVSCPacket()

	chainInfo, err := s.consumerApp.GetConsumerKeeper().GetProviderInfo(s.consumerCtx())
	s.Require().NoError(err)
	s.Require().Equal(chainInfo.Provider.ChainID, "testchain1")
	s.Require().Equal(chainInfo.Consumer.ChainID, "testchain2")
	s.Require().Equal(chainInfo.Provider.ClientID, "07-tendermint-0")
	s.Require().Equal(chainInfo.Consumer.ClientID, "07-tendermint-0")
	s.Require().Equal(chainInfo.Provider.ConnectionID, "connection-0")
	s.Require().Equal(chainInfo.Consumer.ConnectionID, "connection-0")
	s.Require().True(strings.HasPrefix(chainInfo.Provider.ChannelID, "channel-"))
	s.Require().True(strings.HasPrefix(chainInfo.Consumer.ChannelID, "channel-"))
}
