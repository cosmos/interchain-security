package integration

// TestInitTimeout tests the init timeout
func (s *CCVTestSuite) TestInitTimeout() {
	testCases := []struct {
		name      string
		handshake func()
		removed   bool
	}{
		{
			"init times out before INIT", func() {}, true,
		},
		{
			"init times out before TRY", func() {
				// send ChanOpenInit
				err := s.path.EndpointA.ChanOpenInit()
				s.Require().NoError(err)
			}, true,
		},
		{
			"init times out before ACK", func() {
				// send ChanOpenInit
				err := s.path.EndpointA.ChanOpenInit()
				s.Require().NoError(err)
				// send ChanOpenTry
				err = s.path.EndpointB.ChanOpenTry()
				s.Require().NoError(err)
			}, true,
		},
		{
			"init times out before CONFIRM", func() {
				// send ChanOpenInit
				err := s.path.EndpointA.ChanOpenInit()
				s.Require().NoError(err)
				// send ChanOpenTry
				err = s.path.EndpointB.ChanOpenTry()
				s.Require().NoError(err)
				// send ChanOpenAck
				err = s.path.EndpointA.ChanOpenAck()
				s.Require().NoError(err)
			}, true,
		},
		{
			"init completes before timeout", func() {
				// send ChanOpenInit
				err := s.path.EndpointA.ChanOpenInit()
				s.Require().NoError(err)
				// send ChanOpenTry
				err = s.path.EndpointB.ChanOpenTry()
				s.Require().NoError(err)
				// send ChanOpenAck
				err = s.path.EndpointA.ChanOpenAck()
				s.Require().NoError(err)
				// send ChanOpenConfirm
				err = s.path.EndpointB.ChanOpenConfirm()
				s.Require().NoError(err)
			}, false,
		},
	}

	for i, tc := range testCases {
		providerKeeper := s.providerApp.GetProviderKeeper()
		initTimeout := providerKeeper.GetParams(s.providerCtx()).InitTimeoutPeriod
		chainID := s.consumerChain.ChainID

		// check that the init timeout timestamp is set
		_, found := providerKeeper.GetInitTimeoutTimestamp(s.providerCtx(), chainID)
		s.Require().True(found, "cannot find init timeout timestamp; test: %s", tc.name)

		// create connection
		s.coordinator.CreateConnections(s.path)

		// channel opening handshake
		tc.handshake()

		// call NextBlock
		s.providerChain.NextBlock()

		// increment time
		incrementTime(s, initTimeout)

		// check whether the chain was removed
		_, found = providerKeeper.GetConsumerClientID(s.providerCtx(), chainID)
		s.Require().Equal(!tc.removed, found, "unexpected outcome; test: %s", tc.name)

		if tc.removed {
			// check if the chain was properly removed
			s.checkConsumerChainIsRemoved(chainID, false)
		}

		if i+1 < len(testCases) {
			// reset suite to reset provider client
			s.SetupTest()
		}
	}
}
