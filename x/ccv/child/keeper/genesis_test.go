package keeper_test

import (
	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"

	clienttypes "github.com/cosmos/ibc-go/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/modules/core/04-channel/types"

	"github.com/cosmos/interchain-security/app"
	childtypes "github.com/cosmos/interchain-security/x/ccv/child/types"
	parenttypes "github.com/cosmos/interchain-security/x/ccv/parent/types"
	"github.com/cosmos/interchain-security/x/ccv/types"

	abci "github.com/tendermint/tendermint/abci/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

func (suite *KeeperTestSuite) TestGenesis() {
	genesis := suite.childChain.App.(*app.App).ChildKeeper.ExportGenesis(suite.childChain.GetContext())

	suite.Require().Equal(suite.parentClient, genesis.ParentClientState)
	suite.Require().Equal(suite.parentConsState, genesis.ParentConsensusState)

	suite.Require().NotPanics(func() {
		suite.childChain.App.(*app.App).ChildKeeper.InitGenesis(suite.childChain.GetContext(), genesis)
		// reset suite to reset parent client
		suite.SetupTest()
	})

	ctx := suite.childChain.GetContext()
	portId := suite.childChain.App.(*app.App).ChildKeeper.GetPort(ctx)
	suite.Require().Equal(childtypes.PortID, portId)

	clientId, ok := suite.childChain.App.(*app.App).ChildKeeper.GetParentClient(ctx)
	suite.Require().True(ok)
	clientState, ok := suite.childChain.App.GetIBCKeeper().ClientKeeper.GetClientState(ctx, clientId)
	suite.Require().True(ok)
	suite.Require().Equal(genesis.ParentClientState, clientState, "client state not set correctly after InitGenesis")

	suite.SetupCCVChannel()

	origTime := suite.childChain.GetContext().BlockTime()

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
	)
	packet := channeltypes.NewPacket(pd.GetBytes(), 1, parenttypes.PortID, suite.path.EndpointB.ChannelID, childtypes.PortID, suite.path.EndpointA.ChannelID,
		clienttypes.NewHeight(1, 0), 0)
	suite.childChain.App.(*app.App).ChildKeeper.OnRecvPacket(suite.childChain.GetContext(), packet, pd)

	// mocking the fact that child chain validators should be parent chain validators
	// TODO: Fix testing suite so we can initialize both chains with the same validator set
	valUpdates := tmtypes.TM2PB.ValidatorUpdates(suite.parentChain.Vals)

	restartGenesis := suite.childChain.App.(*app.App).ChildKeeper.ExportGenesis(suite.childChain.GetContext())
	restartGenesis.InitialValSet = valUpdates

	// ensure reset genesis is set correctly
	parentChannel := suite.path.EndpointA.ChannelID
	suite.Require().Equal(parentChannel, restartGenesis.ParentChannelId)
	unbondingTime := suite.childChain.App.(*app.App).ChildKeeper.GetUnbondingTime(suite.childChain.GetContext(), 1)
	suite.Require().Equal(uint64(origTime.Add(childtypes.UnbondingTime).UnixNano()), unbondingTime, "unbonding time is not set correctly in genesis")
	unbondingPacket, err := suite.childChain.App.(*app.App).ChildKeeper.GetUnbondingPacket(suite.childChain.GetContext(), 1)
	suite.Require().NoError(err)
	suite.Require().Equal(&packet, unbondingPacket, "unbonding packet is not set correctly in genesis")

	suite.Require().NotPanics(func() {
		suite.childChain.App.(*app.App).ChildKeeper.InitGenesis(suite.childChain.GetContext(), restartGenesis)
	})
}
