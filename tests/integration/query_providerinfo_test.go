package integration

func (s *CCVTestSuite) TestAQueryProviderInfo() {
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
	s.Require().Equal(chainInfo.Provider.ChannelID, "channel-0")
	s.Require().Equal(chainInfo.Consumer.ChannelID, "channel-0")
}
