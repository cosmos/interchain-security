package keeper_test

import (
	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"

	"github.com/cosmos/interchain-security/testutil/simapp"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	"github.com/cosmos/interchain-security/x/ccv/types"

	abci "github.com/tendermint/tendermint/abci/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

func (suite *KeeperTestSuite) TestGenesis() {
	genesis := simapp.GetConsumerKeeper(suite.consumerChain.App).ExportGenesis(suite.consumerChain.GetContext())

	suite.Require().Equal(suite.providerClient, genesis.ProviderClientState)
	suite.Require().Equal(suite.providerConsState, genesis.ProviderConsensusState)

	suite.Require().NotPanics(func() {
		simapp.GetConsumerKeeper(suite.consumerChain.App).InitGenesis(suite.consumerChain.GetContext(), genesis)
		// reset suite to reset provider client
		suite.SetupTest()
	})

	ctx := suite.consumerChain.GetContext()
	portId := simapp.GetConsumerKeeper(suite.consumerChain.App).GetPort(ctx)
	suite.Require().Equal(consumertypes.PortID, portId)

	clientId, ok := simapp.GetConsumerKeeper(suite.consumerChain.App).GetProviderClient(ctx)
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
	pd := types.NewValidatorSetChangePacketData(
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
	packet := channeltypes.NewPacket(pd.GetBytes(), 1, providertypes.PortID, suite.path.EndpointB.ChannelID, consumertypes.PortID, suite.path.EndpointA.ChannelID,
		clienttypes.NewHeight(1, 0), 0)
	simapp.GetConsumerKeeper(suite.consumerChain.App).OnRecvVSCPacket(suite.consumerChain.GetContext(), packet, pd)

	// mocking the fact that consumer chain validators should be provider chain validators
	// TODO: Fix testing suite so we can initialize both chains with the same validator set
	valUpdates := tmtypes.TM2PB.ValidatorUpdates(suite.providerChain.Vals)

	restartGenesis := simapp.GetConsumerKeeper(suite.consumerChain.App).ExportGenesis(suite.consumerChain.GetContext())
	restartGenesis.InitialValSet = valUpdates

	// ensure reset genesis is set correctly
	providerChannel := suite.path.EndpointA.ChannelID
	suite.Require().Equal(providerChannel, restartGenesis.ProviderChannelId)
	maturityTime := simapp.GetConsumerKeeper(suite.consumerChain.App).GetPacketMaturityTime(suite.consumerChain.GetContext(), 1)
	unbondingPeriod, found := simapp.GetConsumerKeeper(suite.consumerChain.App).GetUnbondingTime(suite.ctx)
	suite.Require().True(found)
	suite.Require().Equal(uint64(origTime.Add(unbondingPeriod).UnixNano()), maturityTime, "maturity time is not set correctly in genesis")

	suite.Require().NotPanics(func() {
		simapp.GetConsumerKeeper(suite.consumerChain.App).InitGenesis(suite.consumerChain.GetContext(), restartGenesis)
	})
}
