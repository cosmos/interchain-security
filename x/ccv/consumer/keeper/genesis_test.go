package keeper_test

import (
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	app "github.com/cosmos/interchain-security/app/consumer"
	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	"github.com/cosmos/interchain-security/x/ccv/types"
	abci "github.com/tendermint/tendermint/abci/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

func (suite *KeeperTestSuite) TestGenesis() {

	var (
		slashRequests []consumertypes.SlashRequest = []consumertypes.SlashRequest{
			{Infraction: stakingtypes.Downtime},
			{Infraction: stakingtypes.Downtime},
			{Infraction: stakingtypes.Downtime},
		}
	)

	testCases := []struct {
		malleate            func(*KeeperTestSuite)
		assertExportGenesis func(*KeeperTestSuite, *consumertypes.GenesisState)
		assertInitGenesis   func(*KeeperTestSuite, *consumertypes.GenesisState)
	}{
		{
			malleate: func(s *KeeperTestSuite) {
				s.consumerChain.App.(*app.App).ConsumerKeeper.SetPendingSlashRequests(
					s.consumerChain.GetContext(),
					slashRequests,
				)
			},
			assertExportGenesis: func(s *KeeperTestSuite, genesis *consumertypes.GenesisState) {
				s.Require().Equal(s.providerClient, genesis.ProviderClientState)
				s.Require().Equal(s.providerConsState, genesis.ProviderConsensusState)
				s.Require().EqualValues(slashRequests, genesis.PendingSlashRequests)
			},
			assertInitGenesis: func(s *KeeperTestSuite, genesis *consumertypes.GenesisState) {
				ctx := suite.consumerChain.GetContext()
				portId := suite.consumerChain.App.(*app.App).ConsumerKeeper.GetPort(ctx)
				s.Require().Equal(consumertypes.PortID, portId)

				clientId, ok := s.consumerChain.App.(*app.App).ConsumerKeeper.GetProviderClient(ctx)
				s.Require().True(ok)
				clientState, ok := s.consumerChain.App.GetIBCKeeper().ClientKeeper.GetClientState(ctx, clientId)
				s.Require().True(ok)
				s.Require().Equal(genesis.ProviderClientState, clientState, "client state not set correctly after InitGenesis")
			},
		},
		{
			malleate: func(s *KeeperTestSuite) {
				// reset suite to reset provider client
				s.SetupTest()
				s.SetupCCVChannel()

				// update context
				ctx := s.consumerChain.GetContext()

				// complete CCV channel handshake by sending a first VSC packet
				pd := types.NewValidatorSetChangePacketData([]abci.ValidatorUpdate{}, 1, nil)
				packet := channeltypes.NewPacket(pd.GetBytes(), 1, providertypes.PortID, s.path.EndpointB.ChannelID,
					consumertypes.PortID, s.path.EndpointA.ChannelID,
					clienttypes.NewHeight(1, 0), 0)

				s.consumerChain.App.(*app.App).ConsumerKeeper.OnRecvVSCPacket(ctx, packet, pd)

			},
			assertExportGenesis: func(s *KeeperTestSuite, restartGenesis *consumertypes.GenesisState) {
				// ensure reset genesis is set correctly
				ctx := s.consumerChain.GetContext()

				providerChannel := suite.path.EndpointA.ChannelID
				s.Require().Equal(providerChannel, restartGenesis.ProviderChannelId)
				maturityTime := suite.consumerChain.App.(*app.App).ConsumerKeeper.GetPacketMaturityTime(ctx, 1)
				unbondingPeriod, found := s.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetUnbondingTime(ctx)
				s.Require().True(found)
				s.Require().Equal(uint64(ctx.BlockTime().Add(unbondingPeriod).UnixNano()), maturityTime, "maturity time is not set correctly in genesis")

			},
			assertInitGenesis: func(s *KeeperTestSuite, genesis *consumertypes.GenesisState) {
				ctx := s.consumerChain.GetContext()

				maturityTime := s.consumerChain.App.(*app.App).ConsumerKeeper.GetPacketMaturityTime(ctx, 1)
				suite.Require().NotZero(maturityTime)

			},
		},
	}

	for _, tc := range testCases {

		// suite.Run(tc.name, func() { // remove setup test

		tc.malleate(suite)
		genesis := suite.consumerChain.App.(*app.App).ConsumerKeeper.ExportGenesis(suite.consumerChain.GetContext())
		tc.assertExportGenesis(suite, genesis)

		// manually fill in validator set
		genesis.InitialValSet = tmtypes.TM2PB.ValidatorUpdates(suite.providerChain.Vals)

		suite.Require().NotPanics(func() {
			suite.consumerChain.App.(*app.App).ConsumerKeeper.InitGenesis(suite.consumerChain.GetContext(), genesis)
		})

		tc.assertInitGenesis(suite, genesis)
	}

	// // reset suite to reset provider client
	// suite.SetupTest()

	// ctx := suite.consumerChain.GetContext()
	// portId := suite.consumerChain.App.(*app.App).ConsumerKeeper.GetPort(ctx)
	// suite.Require().Equal(consumertypes.PortID, portId)

	// clientId, ok := suite.consumerChain.App.(*app.App).ConsumerKeeper.GetProviderClient(ctx)
	// suite.Require().True(ok)
	// clientState, ok := suite.consumerChain.App.GetIBCKeeper().ClientKeeper.GetClientState(ctx, clientId)
	// suite.Require().True(ok)
	// suite.Require().Equal(genesis.ProviderClientState, clientState, "client state not set correctly after InitGenesis")

	// suite.SetupCCVChannel()

	// // update context
	// ctx = suite.consumerChain.GetContext()

	// origTime := ctx.BlockTime()

	// // complete CCV channel handshake by sending a first VSC packet
	// pd := types.NewValidatorSetChangePacketData([]abci.ValidatorUpdate{}, 1, nil)
	// packet := channeltypes.NewPacket(pd.GetBytes(), 1, providertypes.PortID, suite.path.EndpointB.ChannelID, consumertypes.PortID, suite.path.EndpointA.ChannelID,
	// 	clienttypes.NewHeight(1, 0), 0)

	// suite.consumerChain.App.(*app.App).ConsumerKeeper.OnRecvVSCPacket(ctx, packet, pd)

	// // ensure provider channel is set
	// _, ok = suite.consumerChain.App.(*app.App).ConsumerKeeper.GetProviderChannel(ctx)
	// suite.Require().True(ok)

	// // export already established
	// restartGenesis := suite.consumerChain.App.(*app.App).ConsumerKeeper.ExportGenesis(ctx)

	// // set ValUpdates using the provider valset
	// restartGenesis.InitialValSet = tmtypes.TM2PB.ValidatorUpdates(suite.providerChain.Vals)

	// fmt.Printf("%#v\n", restartGenesis)

	// // ensure reset genesis is set correctly
	// providerChannel := suite.path.EndpointA.ChannelID
	// suite.Require().Equal(providerChannel, restartGenesis.ProviderChannelId)
	// maturityTime := suite.consumerChain.App.(*app.App).ConsumerKeeper.GetPacketMaturityTime(ctx, 1)
	// unbondingPeriod, found := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetUnbondingTime(ctx)
	// suite.Require().True(found)
	// suite.Require().Equal(uint64(origTime.Add(unbondingPeriod).UnixNano()), maturityTime, "maturity time is not set correctly in genesis")

	// suite.Require().NotPanics(func() {
	// 	suite.consumerChain.App.(*app.App).ConsumerKeeper.InitGenesis(ctx, restartGenesis)
	// })

	// // check maturity time is exported - Set during Restart-Genesis
	// maturityTime = suite.consumerChain.App.(*app.App).ConsumerKeeper.GetPacketMaturityTime(ctx, 1)
	// suite.Require().NotZero(maturityTime)

	// // check provider channel is exported - IBC InitGenesis
	// _, ok = suite.consumerChain.App.(*app.App).ConsumerKeeper.GetProviderChannel(ctx)
	// suite.Require().True(ok)

	// // complete CCV channel handshake by sending a first VSC packet
	// pd = types.NewValidatorSetChangePacketData([]abci.ValidatorUpdate{}, 1, nil)
	// packet = channeltypes.NewPacket(pd.GetBytes(), 1, providertypes.PortID, suite.path.EndpointB.ChannelID, consumertypes.PortID, suite.path.EndpointA.ChannelID,
	// 	clienttypes.NewHeight(1, 0), 0)
	// suite.consumerChain.App.(*app.App).ConsumerKeeper.OnRecvVSCPacket(ctx, packet, pd)

	// // check UnbondingTime is retrieved - retrieved using TmClientState
	// ubdT, ok := suite.consumerChain.App.(*app.App).ConsumerKeeper.GetUnbondingTime(ctx)
	// fmt.Println(ubdT, ok)

	// check HeightToVSCID is retrieved - should be stored during export

	// check outstanding downtime is is retrieved - should be stored during export

	// check CCValidator is retrieved
	// Not need since populated in genesis using initial valset
}
