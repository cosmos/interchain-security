package keeper_test

import (
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	"github.com/cosmos/interchain-security/x/ccv/types"
	abci "github.com/tendermint/tendermint/abci/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

func (suite *KeeperTestSuite) TestGenesis() {
	var (
		vscID         uint64 = 1
		restartHeight uint64
		restartTime   time.Time
		slashRequests []consumertypes.SlashRequest = []consumertypes.SlashRequest{
			{Infraction: stakingtypes.Downtime},
			{Infraction: stakingtypes.Downtime},
			{Infraction: stakingtypes.Downtime},
		}
		consAddr sdk.ConsAddress
	)

	testCases := []struct {
		name                string
		malleate            func(*KeeperTestSuite)
		assertExportGenesis func(*KeeperTestSuite, *consumertypes.GenesisState)
		assertInitGenesis   func(*KeeperTestSuite, *consumertypes.GenesisState)
	}{
		{
			name: "restart a new chain",
			malleate: func(s *KeeperTestSuite) {
				s.consumerChain.App.(*appConsumer.App).ConsumerKeeper.SetPendingSlashRequests(
					s.consumerChain.GetContext(),
					slashRequests,
				)
			},
			assertExportGenesis: func(s *KeeperTestSuite, genesis *consumertypes.GenesisState) {
				// check that the client and consensus states are exported
				s.Require().Equal(s.providerClient, genesis.ProviderClientState)
				s.Require().Equal(s.providerConsState, genesis.ProviderConsensusState)
				s.Require().EqualValues(slashRequests, genesis.PendingSlashRequests)
			},
			assertInitGenesis: func(s *KeeperTestSuite, genesis *consumertypes.GenesisState) {
				ctx := suite.consumerChain.GetContext()

				portId := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetPort(ctx)
				s.Require().Equal(consumertypes.PortID, portId)

				_, found := s.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetUnbondingTime(ctx)
				s.Require().True(found)

				clientId, ok := s.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetProviderClient(ctx)
				s.Require().True(ok)
				clientState, ok := s.consumerChain.App.GetIBCKeeper().ClientKeeper.GetClientState(ctx, clientId)
				s.Require().True(ok)
				s.Require().Equal(genesis.ProviderClientState, clientState, "client state not set correctly after InitGenesis")
			},
		},
		{
			name: "restart a chain with channel already established",
			malleate: func(s *KeeperTestSuite) {
				// reset suite to reset provider client
				s.SetupTest()
				s.SetupCCVChannel()

				// update context
				ctx := s.consumerChain.GetContext()
				restartHeight = uint64(ctx.BlockHeight())
				restartTime = ctx.BlockTime()

				// complete CCV channel handshake by sending a first VSC packet
				pd := types.NewValidatorSetChangePacketData([]abci.ValidatorUpdate{}, vscID, nil)
				packet := channeltypes.NewPacket(pd.GetBytes(), 1, providertypes.PortID, s.path.EndpointB.ChannelID,
					consumertypes.PortID, s.path.EndpointA.ChannelID,
					clienttypes.NewHeight(1, 0), 0)

				s.consumerChain.App.(*appConsumer.App).ConsumerKeeper.OnRecvVSCPacket(ctx, packet, pd)

				vals := s.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetAllCCValidator(ctx)
				consAddr = sdk.ConsAddress(vals[0].Address)
				s.consumerChain.App.(*appConsumer.App).ConsumerKeeper.SetOutstandingDowntime(ctx, consAddr)
			},
			assertExportGenesis: func(s *KeeperTestSuite, restartGenesis *consumertypes.GenesisState) {
				ctx := s.consumerChain.GetContext()

				// check that the CCV states are exported
				providerChannel := suite.path.EndpointA.ChannelID
				s.Require().Equal(providerChannel, restartGenesis.ProviderChannelId)

				clientID := suite.path.EndpointA.ClientID
				s.Require().Equal(clientID, restartGenesis.ProviderClientId)

				suite.Require().NotNil(restartGenesis.GetMaturingPackets())

				heighToVSCID := restartGenesis.HeightToValsetUpdateId
				suite.Require().NotNil(heighToVSCID)
				suite.Require().Equal(vscID, heighToVSCID[len(heighToVSCID)-1].ValsetUpdateId)

				suite.Require().NotNil(restartGenesis.OutstandingDowntimeSlashing)
				suite.Require().Equal(consAddr.String(), restartGenesis.OutstandingDowntimeSlashing[0].GetValidatorConsensusAddress())
				s.Require().Equal(s.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetParams(ctx), restartGenesis.Params)
			},
			assertInitGenesis: func(s *KeeperTestSuite, genesis *consumertypes.GenesisState) {
				ctx := s.consumerChain.GetContext()

				_, found := s.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetUnbondingTime(ctx)
				s.Require().True(found)

				s.consumerChain.App.(*appConsumer.App).ConsumerKeeper.IterateHeightToValsetUpdateID(ctx, func(h, v uint64) bool {
					return true
				})
				gotVSCID := s.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetHeightValsetUpdateID(ctx, uint64(restartHeight+1))
				s.Require().Equal(vscID, gotVSCID)

				unbondingPeriod, found := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetUnbondingTime(ctx)
				suite.Require().True(found)

				maturityTime := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetPacketMaturityTime(ctx, vscID)
				s.Require().NotZero(maturityTime)

				suite.Require().Equal(uint64(restartTime.Add(unbondingPeriod).UnixNano()), maturityTime, "maturity time is not set correctly in genesis")
				s.Require().Equal(genesis.Params, s.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetParams(ctx))
			},
		},
	}

	for _, tc := range testCases {
		suite.Run(tc.name, func() {
			tc.malleate(suite)

			genesis := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.ExportGenesis(suite.consumerChain.GetContext())
			tc.assertExportGenesis(suite, genesis)

			// reset context
			suite.SetupTest()

			// manually fill in validator set
			genesis.InitialValSet = tmtypes.TM2PB.ValidatorUpdates(suite.providerChain.Vals)

			// init genesis
			suite.Require().NotPanics(func() {
				suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.InitGenesis(suite.consumerChain.GetContext(), genesis)
			})

			tc.assertInitGenesis(suite, genesis)
		})
	}
}
