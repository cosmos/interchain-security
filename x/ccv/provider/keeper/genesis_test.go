package keeper_test

import (
	"fmt"

	appProvider "github.com/cosmos/interchain-security/app/provider"
)

func (suite *KeeperTestSuite) TestGenesis() {
	// set some chain-channel pairs before exporting
	ctx := suite.providerChain.GetContext()
	for i := 0; i < 4; i++ {
		suite.providerChain.App.(*appProvider.App).ProviderKeeper.SetChainToChannel(ctx, fmt.Sprintf("chainid-%d", i), fmt.Sprintf("channelid-%d", i))
		suite.providerChain.App.(*appProvider.App).ProviderKeeper.SetChannelToChain(ctx, fmt.Sprintf("channelid-%d", i), fmt.Sprintf("chainid-%d", i))
	}

	genState := suite.providerChain.App.(*appProvider.App).ProviderKeeper.ExportGenesis(suite.providerChain.GetContext())

	suite.consumerChain.App.(*appProvider.App).ProviderKeeper.InitGenesis(suite.consumerChain.GetContext(), genState)

	ctx = suite.consumerChain.GetContext()
	for i := 0; i < 4; i++ {
		expectedChainId := fmt.Sprintf("chainid-%d", i)
		expectedChannelId := fmt.Sprintf("channelid-%d", i)
		channelID, channelOk := suite.consumerChain.App.(*appProvider.App).ProviderKeeper.GetChainToChannel(ctx, expectedChainId)
		chainID, chainOk := suite.consumerChain.App.(*appProvider.App).ProviderKeeper.GetChannelToChain(ctx, expectedChannelId)
		suite.Require().True(channelOk)
		suite.Require().True(chainOk)
		suite.Require().Equal(expectedChainId, chainID, "did not store correct chain id for given channel id")
		suite.Require().Equal(expectedChannelId, channelID, "did not store correct channel id for given chain id")
	}
}
