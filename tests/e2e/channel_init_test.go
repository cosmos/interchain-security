package e2e_test

import (
	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"

	app "github.com/cosmos/interchain-security/app/consumer"
	appProvider "github.com/cosmos/interchain-security/app/provider"

	tmtypes "github.com/tendermint/tendermint/types"

	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"

	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"

	abci "github.com/tendermint/tendermint/abci/types"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
)

func (suite *CCVTestSuite) TestConsumerGenesis() {
	genesis := suite.consumerChain.App.(*app.App).ConsumerKeeper.ExportGenesis(suite.consumerChain.GetContext())

	suite.Require().Equal(suite.providerClient, genesis.ProviderClientState)
	suite.Require().Equal(suite.providerConsState, genesis.ProviderConsensusState)

	suite.Require().NotPanics(func() {
		suite.consumerChain.App.(*app.App).ConsumerKeeper.InitGenesis(suite.consumerChain.GetContext(), genesis)
		// reset suite to reset provider client
		suite.SetupTest()
	})

	ctx := suite.consumerChain.GetContext()
	portId := suite.consumerChain.App.(*app.App).ConsumerKeeper.GetPort(ctx)
	suite.Require().Equal(ccv.ConsumerPortID, portId)

	clientId, ok := suite.consumerChain.App.(*app.App).ConsumerKeeper.GetProviderClientID(ctx)
	suite.Require().True(ok)
	clientState, ok := suite.consumerChain.App.GetIBCKeeper().ClientKeeper.GetClientState(ctx, clientId)
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
	suite.consumerChain.App.(*app.App).ConsumerKeeper.OnRecvVSCPacket(suite.consumerChain.GetContext(), packet, pd)
	valUpdates := tmtypes.TM2PB.ValidatorUpdates(suite.providerChain.Vals)

	restartGenesis := suite.consumerChain.App.(*app.App).ConsumerKeeper.ExportGenesis(suite.consumerChain.GetContext())
	suite.Require().Equal(valUpdates, restartGenesis.InitialValSet)

	// ensure reset genesis is set correctly
	providerChannel := suite.path.EndpointA.ChannelID
	suite.Require().Equal(providerChannel, restartGenesis.ProviderChannelId)
	maturityTime := suite.consumerChain.App.(*app.App).ConsumerKeeper.GetPacketMaturityTime(suite.consumerChain.GetContext(), 1)
	unbondingPeriod, found := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetUnbondingTime(suite.consumerCtx())
	suite.Require().True(found)
	suite.Require().Equal(uint64(origTime.Add(unbondingPeriod).UnixNano()), maturityTime, "maturity time is not set correctly in genesis")

	suite.Require().NotPanics(func() {
		suite.consumerChain.App.(*app.App).ConsumerKeeper.InitGenesis(suite.consumerChain.GetContext(), restartGenesis)
	})
}

// TestProviderClientMatches tests that the provider client managed by the consumer keeper matches the client keeper's client state
func (suite *CCVTestSuite) TestProviderClientMatches() {
	providerClientID, ok := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetProviderClientID(suite.consumerCtx())
	suite.Require().True(ok)

	clientState, _ := suite.consumerChain.App.GetIBCKeeper().ClientKeeper.GetClientState(suite.consumerCtx(), providerClientID)
	suite.Require().Equal(suite.providerClient, clientState, "stored client state does not match genesis provider client")
}

// TestInitTimeoutNoInit tests the init timeout works when
// the channel opening handshake didn't started yet
func (suite *CCVTestSuite) TestInitTimeoutNoInit() {
	providerKeeper := suite.providerChain.App.(*appProvider.App).ProviderKeeper
	initTimeout := providerKeeper.GetParams(suite.providerCtx()).InitTimeoutPeriod
	chainID := suite.consumerChain.ChainID

	// get init timeout timestamp
	ts, found := providerKeeper.GetInitTimeoutTimestamp(suite.providerCtx(), chainID)
	suite.Require().True(found)
	expectedTs := suite.providerCtx().BlockTime().Add(initTimeout)
	suite.Require().Equal(uint64(expectedTs.UnixNano()), ts)

	suite.coordinator.CreateConnections(suite.path)

	// call NextBlock
	suite.providerChain.NextBlock()

	// increment time
	incrementTimeBy(suite, initTimeout)

	// check if the chain was removed
	suite.checkConsumerChainIsRemoved(chainID, false, false)
}

// TestInitTimeoutNoTry tests the init timeout works when
// the channel opening handshake started, but no ChanOpenTry was sent
func (suite *CCVTestSuite) TestInitTimeoutNoTry() {
	providerKeeper := suite.providerChain.App.(*appProvider.App).ProviderKeeper
	initTimeout := providerKeeper.GetParams(suite.providerCtx()).InitTimeoutPeriod
	chainID := suite.consumerChain.ChainID

	// get init timeout timestamp
	ts, found := providerKeeper.GetInitTimeoutTimestamp(suite.providerCtx(), chainID)
	suite.Require().True(found)
	expectedTs := suite.providerCtx().BlockTime().Add(initTimeout)
	suite.Require().Equal(uint64(expectedTs.UnixNano()), ts)

	// send ChanOpenInit
	suite.coordinator.CreateConnections(suite.path)
	err := suite.path.EndpointA.ChanOpenInit()
	suite.Require().NoError(err)

	// call NextBlock
	suite.providerChain.NextBlock()

	// increment time
	incrementTimeBy(suite, initTimeout)

	// check if the chain was removed
	suite.checkConsumerChainIsRemoved(chainID, false, false)
}

// TestInitTimeoutNoAck tests the init timeout works when
// the channel opening handshake started, but no ChanOpenAck was sent
func (suite *CCVTestSuite) TestInitTimeoutNoAck() {
	providerKeeper := suite.providerChain.App.(*appProvider.App).ProviderKeeper
	initTimeout := providerKeeper.GetParams(suite.providerCtx()).InitTimeoutPeriod
	chainID := suite.consumerChain.ChainID

	// get init timeout timestamp
	ts, found := providerKeeper.GetInitTimeoutTimestamp(suite.providerCtx(), chainID)
	suite.Require().True(found)
	expectedTs := suite.providerCtx().BlockTime().Add(initTimeout)
	suite.Require().Equal(uint64(expectedTs.UnixNano()), ts)

	// send ChanOpenInit, ChanOpenTry
	suite.coordinator.CreateConnections(suite.path)
	err := suite.path.EndpointA.ChanOpenInit()
	suite.Require().NoError(err)
	err = suite.path.EndpointB.ChanOpenTry()
	suite.Require().NoError(err)

	// call NextBlock
	suite.providerChain.NextBlock()

	// increment time
	incrementTimeBy(suite, initTimeout)

	// check if the chain was removed
	suite.checkConsumerChainIsRemoved(chainID, false, false)
}

// TestInitTimeoutNoConfirm tests the init timeout works when
// the channel opening handshake started, but no ChanOpenConfirm was sent
func (suite *CCVTestSuite) TestInitTimeoutNoConfirm() {
	providerKeeper := suite.providerChain.App.(*appProvider.App).ProviderKeeper
	initTimeout := providerKeeper.GetParams(suite.providerCtx()).InitTimeoutPeriod
	chainID := suite.consumerChain.ChainID

	// get init timeout timestamp
	ts, found := providerKeeper.GetInitTimeoutTimestamp(suite.providerCtx(), chainID)
	suite.Require().True(found)
	expectedTs := suite.providerCtx().BlockTime().Add(initTimeout)
	suite.Require().Equal(uint64(expectedTs.UnixNano()), ts)

	// send ChanOpenInit, ChanOpenTry, ChanOpenAck
	suite.coordinator.CreateConnections(suite.path)
	err := suite.path.EndpointA.ChanOpenInit()
	suite.Require().NoError(err)
	err = suite.path.EndpointB.ChanOpenTry()
	suite.Require().NoError(err)
	err = suite.path.EndpointA.ChanOpenAck()
	suite.Require().NoError(err)

	// call NextBlock
	suite.providerChain.NextBlock()

	// increment time
	incrementTimeBy(suite, initTimeout)

	// check if the chain was removed
	suite.checkConsumerChainIsRemoved(chainID, false, false)
}

// TestInitTimeoutHandshakeCompleted tests the init timeout works when
// the channel opening handshake completes
func (suite *CCVTestSuite) TestInitTimeoutHandshakeCompleted() {
	providerKeeper := suite.providerChain.App.(*appProvider.App).ProviderKeeper
	initTimeout := providerKeeper.GetParams(suite.providerCtx()).InitTimeoutPeriod
	chainID := suite.consumerChain.ChainID

	// get init timeout timestamp
	ts, found := providerKeeper.GetInitTimeoutTimestamp(suite.providerCtx(), chainID)
	suite.Require().True(found)
	expectedTs := suite.providerCtx().BlockTime().Add(initTimeout)
	suite.Require().Equal(uint64(expectedTs.UnixNano()), ts)

	// complete CCV channel setup
	suite.SetupCCVChannel()

	// check that the init timeout timestamp was removed
	_, found = providerKeeper.GetInitTimeoutTimestamp(suite.providerCtx(), chainID)
	suite.Require().False(found)

	// call NextBlock
	suite.providerChain.NextBlock()

	// increment time
	incrementTimeBy(suite, initTimeout)

	// check that the chain was not removed
	_, found = providerKeeper.GetConsumerClientId(suite.providerCtx(), chainID)
	suite.Require().True(found)
}
