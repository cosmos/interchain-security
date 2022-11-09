package e2e

import (
	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"

	tmtypes "github.com/tendermint/tendermint/types"

	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"

	ccv "github.com/cosmos/interchain-security/x/ccv/types"

	abci "github.com/tendermint/tendermint/abci/types"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
)

func (suite *CCVTestSuite) TestConsumerGenesis() {

	consumerKeeper := suite.consumerApp.GetConsumerKeeper()

	genesis := consumerKeeper.ExportGenesis(suite.consumerChain.GetContext())

	// Confirm that client and cons state are exported from consumer keeper properly
	consumerEndpointClientState, consumerEndpointConsState := suite.GetConsumerEndpointClientAndConsState()
	suite.Require().Equal(consumerEndpointClientState, genesis.ProviderClientState)
	suite.Require().Equal(consumerEndpointConsState, genesis.ProviderConsensusState)

	suite.Require().NotPanics(func() {
		consumerKeeper.InitGenesis(suite.consumerChain.GetContext(), genesis)
		// reset suite to reset provider client
		suite.SetupTest()
		consumerKeeper = suite.consumerApp.GetConsumerKeeper()
	})

	ctx := suite.consumerChain.GetContext()
	portId := consumerKeeper.GetPort(ctx)
	suite.Require().Equal(ccv.ConsumerPortID, portId)

	clientId, ok := consumerKeeper.GetProviderClientID(ctx)
	suite.Require().True(ok)
	clientState, ok := suite.consumerApp.GetIBCKeeper().ClientKeeper.GetClientState(ctx, clientId)
	suite.Require().True(ok)
	suite.Require().Equal(genesis.ProviderClientState, clientState, "client state not set correctly after InitGenesis")

	suite.SetupCCVChannel()

	origTime := suite.consumerChain.GetContext().BlockTime()

	pk1, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
	suite.Require().NoError(err)
	pk2, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
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
	packet := channeltypes.NewPacket(pd.GetBytes(), 1,
		ccv.ProviderPortID, suite.path.EndpointB.ChannelID,
		ccv.ConsumerPortID, suite.path.EndpointA.ChannelID,
		clienttypes.NewHeight(1, 0), 0)
	consumerKeeper.OnRecvVSCPacket(suite.consumerChain.GetContext(), packet, pd)
	valUpdates := tmtypes.TM2PB.ValidatorUpdates(suite.providerChain.Vals)

	restartGenesis := consumerKeeper.ExportGenesis(suite.consumerChain.GetContext())
	suite.Require().Equal(valUpdates, restartGenesis.InitialValSet)

	// ensure reset genesis is set correctly
	providerChannel := suite.path.EndpointA.ChannelID
	suite.Require().Equal(providerChannel, restartGenesis.ProviderChannelId)
	maturityTime := consumerKeeper.GetPacketMaturityTime(suite.consumerChain.GetContext(), 1)
	unbondingPeriod := consumerKeeper.GetUnbondingPeriod(suite.consumerCtx())
	suite.Require().Equal(uint64(origTime.Add(unbondingPeriod).UnixNano()), maturityTime, "maturity time is not set correctly in genesis")

	suite.Require().NotPanics(func() {
		consumerKeeper.InitGenesis(suite.consumerChain.GetContext(), restartGenesis)
	})
}

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
		initTimeout := providerKeeper.GetParams(suite.providerCtx()).InitTimeoutPeriod
		chainID := suite.consumerChain.ChainID

		// get init timeout timestamp
		ts, found := providerKeeper.GetInitTimeoutTimestamp(suite.providerCtx(), chainID)
		suite.Require().True(found, "cannot find init timeout timestamp; test: %s", tc.name)
		expectedTs := suite.providerCtx().BlockTime().Add(initTimeout)
		suite.Require().Equal(uint64(expectedTs.UnixNano()), ts, "unexpected init timeout timestamp; test: %s", tc.name)

		// create connection
		suite.coordinator.CreateConnections(suite.path)

		// channel opening handshake
		tc.handshake()

		// call NextBlock
		suite.providerChain.NextBlock()

		// increment time
		incrementTimeBy(suite, initTimeout)

		// check whether the chain was removed
		_, found = providerKeeper.GetConsumerClientId(suite.providerCtx(), chainID)
		suite.Require().Equal(!tc.removed, found, "unexpected outcome; test: %s", tc.name)

		if tc.removed {
			// check if the chain was properly removed
			suite.checkConsumerChainIsRemoved(chainID, false, false)
		}

		if i+1 < len(testCases) {
			// reset suite to reset provider client
			suite.SetupTest()
		}
	}
}
