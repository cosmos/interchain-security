package e2e_test

import (
	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"

	app "github.com/cosmos/interchain-security/app/consumer"

	tmtypes "github.com/tendermint/tendermint/types"

	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"

	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"

	abci "github.com/tendermint/tendermint/abci/types"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
)

func (suite *ConsumerKeeperTestSuite) TestConsumerGenesis() {
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
	unbondingPeriod, found := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetUnbondingTime(suite.ctx)
	suite.Require().True(found)
	suite.Require().Equal(uint64(origTime.Add(unbondingPeriod).UnixNano()), maturityTime, "maturity time is not set correctly in genesis")

	suite.Require().NotPanics(func() {
		suite.consumerChain.App.(*app.App).ConsumerKeeper.InitGenesis(suite.consumerChain.GetContext(), restartGenesis)
	})
}

// TestProviderClientMatches tests that the provider client managed by the consumer keeper matches the client keeper's client state
func (suite *ConsumerKeeperTestSuite) TestProviderClientMatches() {
	providerClientID, ok := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetProviderClientID(suite.ctx)
	suite.Require().True(ok)

	clientState, _ := suite.consumerChain.App.GetIBCKeeper().ClientKeeper.GetClientState(suite.ctx, providerClientID)
	suite.Require().Equal(suite.providerClient, clientState, "stored client state does not match genesis provider client")
}
