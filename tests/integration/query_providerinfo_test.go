package integration

// TestQueryProviderInfo tests the results of GetProviderInfo method.
//
// Test cases:
// 1. Positive test - verifies that GetProviderInfo returns correct information about:
//   - Chain IDs for both provider and consumer
//   - Client IDs
//   - Connection IDs
//   - Channel IDs
//   - Provider's staking denomination
//   - Channel version
// 2. Negative test - verifies behavior when CCV channel is not established
func (s *CCVTestSuite) TestQueryProviderInfo() {
	// Test case 1: Positive test with established CCV channel
	s.SetupCCVChannel(s.path)
	s.SendEmptyVSCPacket()

	chainInfo, err := s.consumerApp.GetConsumerKeeper().GetProviderInfo(s.consumerCtx())
	s.Require().NoError(err)
	
	// Chain ID verification
	s.Require().Equal(chainInfo.Provider.ChainID, "testchain1")
	s.Require().Equal(chainInfo.Consumer.ChainID, "testchain2")
	
	// Client ID verification
	s.Require().Equal(chainInfo.Provider.ClientID, "07-tendermint-0")
	s.Require().Equal(chainInfo.Consumer.ClientID, "07-tendermint-0")
	
	// Connection ID verification
	s.Require().Equal(chainInfo.Provider.ConnectionID, "connection-0")
	s.Require().Equal(chainInfo.Consumer.ConnectionID, "connection-0")
	
	// Channel ID verification
	s.Require().Equal(chainInfo.Provider.ChannelID, "channel-0")
	s.Require().Equal(chainInfo.Consumer.ChannelID, "channel-0")
	
	// Additional verifications
	s.Require().Equal(chainInfo.Provider.StakingDenom, "stake", "Provider staking denomination should be 'stake'")
	s.Require().Equal(chainInfo.ChannelVersion, "1", "Channel version should be '1'")

	// Test case 2: Negative test - before CCV channel setup
	s.SetupTest()
	chainInfo, err = s.consumerApp.GetConsumerKeeper().GetProviderInfo(s.consumerCtx())
	s.Require().Error(err, "GetProviderInfo should return error when CCV channel is not established")
	s.Require().Nil(chainInfo, "ChainInfo should be nil when CCV channel is not established")
}
