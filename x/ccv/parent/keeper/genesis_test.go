package keeper_test

import (
	"fmt"

	childApp "github.com/cosmos/interchain-security/app_child"
	parentApp "github.com/cosmos/interchain-security/app_parent"
	"github.com/cosmos/interchain-security/x/ccv/types"
)

func (suite *KeeperTestSuite) TestGenesis() {
	// set some chain-channel pairs before exporting
	ctx := suite.parentChain.GetContext()
	for i := 0; i < 4; i++ {
		suite.parentChain.App.(*parentApp.App).ParentKeeper.SetChainToChannel(ctx, fmt.Sprintf("chainid-%d", i), fmt.Sprintf("channelid-%d", i))
		suite.parentChain.App.(*parentApp.App).ParentKeeper.SetChannelToChain(ctx, fmt.Sprintf("channelid-%d", i), fmt.Sprintf("chainid-%d", i))
		suite.parentChain.App.(*parentApp.App).ParentKeeper.SetChannelStatus(ctx, fmt.Sprintf("channelid-%d", i), types.Status(i))
	}

	genState := suite.parentChain.App.(*parentApp.App).ParentKeeper.ExportGenesis(suite.parentChain.GetContext())

	suite.childChain.App.(*childApp.App).ParentKeeper.InitGenesis(suite.childChain.GetContext(), genState)

	ctx = suite.childChain.GetContext()
	for i := 0; i < 4; i++ {
		expectedChainId := fmt.Sprintf("chainid-%d", i)
		expectedChannelId := fmt.Sprintf("channelid-%d", i)
		channelID, channelOk := suite.childChain.App.(*childApp.App).ParentKeeper.GetChainToChannel(ctx, expectedChainId)
		chainID, chainOk := suite.childChain.App.(*childApp.App).ParentKeeper.GetChannelToChain(ctx, expectedChannelId)
		suite.Require().True(channelOk)
		suite.Require().True(chainOk)
		suite.Require().Equal(expectedChainId, chainID, "did not store correct chain id for given channel id")
		suite.Require().Equal(expectedChannelId, channelID, "did not store correct channel id for given chain id")

		status := suite.childChain.App.(*childApp.App).ParentKeeper.GetChannelStatus(ctx, channelID)
		suite.Require().Equal(types.Status(i), status, "status is unexpected for given channel id: %s", channelID)
	}
}
