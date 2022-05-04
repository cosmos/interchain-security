package keeper_test

import (
	"fmt"

	appConsumer "github.com/cosmos/interchain-security/app_consumer"
	appProvider "github.com/cosmos/interchain-security/app_provider"
	"github.com/cosmos/interchain-security/x/ccv/types"
)

func (suite *KeeperTestSuite) TestGenesis() {
	// set some chain-channel pairs before exporting
	ctx := suite.providerChain.GetContext()
	for i := 0; i < 4; i++ {
		suite.providerChain.App.(*appProvider.App).ProviderKeeper.SetChainToChannel(ctx, fmt.Sprintf("chainid-%d", i), fmt.Sprintf("channelid-%d", i))
		suite.providerChain.App.(*appProvider.App).ProviderKeeper.SetChannelToChain(ctx, fmt.Sprintf("channelid-%d", i), fmt.Sprintf("chainid-%d", i))
		suite.providerChain.App.(*appProvider.App).ProviderKeeper.SetChannelStatus(ctx, fmt.Sprintf("channelid-%d", i), types.Status(i))
	}

	genState := suite.providerChain.App.(*appProvider.App).ProviderKeeper.ExportGenesis(suite.providerChain.GetContext())

	suite.consumerChain.App.(*appConsumer.App).ProviderKeeper.InitGenesis(suite.consumerChain.GetContext(), genState)

	ctx = suite.consumerChain.GetContext()
	for i := 0; i < 4; i++ {
		expectedChainId := fmt.Sprintf("chainid-%d", i)
		expectedChannelId := fmt.Sprintf("channelid-%d", i)
		channelID, channelOk := suite.consumerChain.App.(*appConsumer.App).ProviderKeeper.GetChainToChannel(ctx, expectedChainId)
		chainID, chainOk := suite.consumerChain.App.(*appConsumer.App).ProviderKeeper.GetChannelToChain(ctx, expectedChannelId)
		suite.Require().True(channelOk)
		suite.Require().True(chainOk)
		suite.Require().Equal(expectedChainId, chainID, "did not store correct chain id for given channel id")
		suite.Require().Equal(expectedChannelId, channelID, "did not store correct channel id for given chain id")

		status := suite.consumerChain.App.(*appConsumer.App).ProviderKeeper.GetChannelStatus(ctx, channelID)
		suite.Require().Equal(types.Status(i), status, "status is unexpected for given channel id: %s", channelID)
	}
}
