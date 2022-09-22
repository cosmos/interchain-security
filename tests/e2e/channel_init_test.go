package e2e_test

import (
	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"

	app "github.com/cosmos/interchain-security/app/consumer"

	"fmt"

	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	tmtypes "github.com/tendermint/tendermint/types"

	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"

	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	"github.com/cosmos/interchain-security/x/ccv/consumer"
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

	// mocking the fact that consumer chain validators should be provider chain validators
	// TODO: Fix testing suite so we can initialize both chains with the same validator set
	valUpdates := tmtypes.TM2PB.ValidatorUpdates(suite.providerChain.Vals)

	restartGenesis := suite.consumerChain.App.(*app.App).ConsumerKeeper.ExportGenesis(suite.consumerChain.GetContext())
	restartGenesis.InitialValSet = valUpdates

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

// TODO: unit and spec tags
func (suite *ConsumerTestSuite) TestOnChanOpenTry() {
	// OnOpenTry must error even with correct arguments
	consumerModule := consumer.NewAppModule(suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper)
	_, err := consumerModule.OnChanOpenTry(
		suite.ctx,
		channeltypes.ORDERED,
		[]string{"connection-1"},
		ccv.ConsumerPortID,
		"channel-1",
		nil,
		channeltypes.NewCounterparty(ccv.ProviderPortID, "channel-1"),
		ccv.Version,
	)
	suite.Require().Error(err, "OnChanOpenTry callback must error on consumer chain")
}

// TODO: unit and spec tags
// TestOnChanOpenAck tests the consumer module's OnChanOpenAck implementation against the spec:
// https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-ccf-coack1
func (suite *ConsumerTestSuite) TestOnChanOpenAck() {

	var (
		portID     string
		channelID  string
		metadataBz []byte
		metadata   providertypes.HandshakeMetadata
		err        error
	)
	testCases := []struct {
		name     string
		malleate func()
		expPass  bool
	}{
		{
			"success", func() {}, true,
		},
		{
			"invalid: provider channel already established",
			func() {
				suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.SetProviderChannel(suite.ctx, "channel-2")
			}, false,
		},
		{
			"invalid: cannot unmarshal ack metadata ",
			func() {
				metadataBz = []byte{78, 89, 20}
			}, false,
		},
		{
			"invalid: mismatched versions",
			func() {
				// Set counter party version to an invalid value, passed as marshaled metadata
				metadata.Version = "invalidVersion"
				metadataBz, err = (&metadata).Marshal()
				suite.Require().NoError(err)
			}, false,
		},
		// See ConsumerKeeper.GetConnectionHops as to why portID and channelID must be correct
		{
			"invalid: portID ",
			func() {
				portID = "invalidPort"
			}, false,
		},
		{
			"invalid: channelID ",
			func() {
				channelID = "invalidChan"
			}, false,
		},
	}

	for _, tc := range testCases {
		tc := tc
		suite.Run(fmt.Sprintf("Case: %s", tc.name), func() {
			suite.SetupTest() // reset
			portID = ccv.ConsumerPortID
			channelID = "channel-1"
			counterChannelID := "channel-2" // per spec this is not required by onChanOpenAck()
			suite.path.EndpointA.ChannelID = channelID

			// Set INIT channel on consumer chain
			suite.consumerChain.App.GetIBCKeeper().ChannelKeeper.SetChannel(
				suite.ctx,
				ccv.ConsumerPortID,
				channelID,
				channeltypes.NewChannel(
					channeltypes.INIT,
					channeltypes.ORDERED,
					channeltypes.NewCounterparty(ccv.ProviderPortID, ""),
					[]string{suite.path.EndpointA.ConnectionID},
					suite.path.EndpointA.ChannelConfig.Version,
				),
			)

			consumerModule := consumer.NewAppModule(
				suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper)

			metadata := providertypes.HandshakeMetadata{
				ProviderFeePoolAddr: "", // dummy address used
				Version:             suite.path.EndpointB.ChannelConfig.Version,
			}

			metadataBz, err = (&metadata).Marshal()
			suite.Require().NoError(err)

			tc.malleate() // Explicitly change fields already defined

			err = consumerModule.OnChanOpenAck(
				suite.ctx,
				portID,
				channelID,
				counterChannelID,
				string(metadataBz),
			)

			if tc.expPass {
				suite.Require().NoError(err)
			} else {
				suite.Require().Error(err)
			}
		})
	}
}
