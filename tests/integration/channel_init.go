package integration

// TestInitTimeout tests the init timeout
func (suite *CCVTestSuite) TestInitTimeout() {
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
				err := suite.path.EndpointA.ChanOpenInit()
				suite.Require().NoError(err)
			}, true,
		},
		{
			"init times out before ACK", func() {
				// send ChanOpenInit
				err := suite.path.EndpointA.ChanOpenInit()
				suite.Require().NoError(err)
				// send ChanOpenTry
				err = suite.path.EndpointB.ChanOpenTry()
				suite.Require().NoError(err)
			}, true,
		},
		{
			"init times out before CONFIRM", func() {
				// send ChanOpenInit
				err := suite.path.EndpointA.ChanOpenInit()
				suite.Require().NoError(err)
				// send ChanOpenTry
				err = suite.path.EndpointB.ChanOpenTry()
				suite.Require().NoError(err)
				// send ChanOpenAck
				err = suite.path.EndpointA.ChanOpenAck()
				suite.Require().NoError(err)
			}, true,
		},
		{
			"init completes before timeout", func() {
				// send ChanOpenInit
				err := suite.path.EndpointA.ChanOpenInit()
				suite.Require().NoError(err)
				// send ChanOpenTry
				err = suite.path.EndpointB.ChanOpenTry()
				suite.Require().NoError(err)
				// send ChanOpenAck
				err = suite.path.EndpointA.ChanOpenAck()
				suite.Require().NoError(err)
				// send ChanOpenConfirm
				err = suite.path.EndpointB.ChanOpenConfirm()
				suite.Require().NoError(err)
			}, false,
		},
	}

	for i, tc := range testCases {
		providerKeeper := suite.providerApp.GetProviderKeeper()
		params, err := providerKeeper.GetParams(suite.providerCtx())
		suite.Require().NoError(err)
		initTimeout := params.InitTimeoutPeriod

		chainID := suite.consumerChain.ChainID

		// check that the init timeout timestamp is set
		_, found := providerKeeper.GetInitTimeoutTimestamp(suite.providerCtx(), chainID)
		suite.Require().True(found, "cannot find init timeout timestamp; test: %s", tc.name)

		// create connection
		suite.coordinator.CreateConnections(suite.path)

		// channel opening handshake
		tc.handshake()

		// call NextBlock
		suite.providerChain.NextBlock()

		// increment time
		incrementTime(suite, initTimeout)

		// check whether the chain was removed
		_, found = providerKeeper.GetConsumerClientId(suite.providerCtx(), chainID)
		suite.Require().Equal(!tc.removed, found, "unexpected outcome; test: %s", tc.name)

		if tc.removed {
			// check if the chain was properly removed
			suite.checkConsumerChainIsRemoved(chainID, false)
		}

		if i+1 < len(testCases) {
			// reset suite to reset provider client
			suite.SetupTest()
		}
	}
}
