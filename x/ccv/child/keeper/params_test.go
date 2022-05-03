package keeper_test

import (
	parentApp "github.com/cosmos/interchain-security/app_parent"
	"github.com/cosmos/interchain-security/x/ccv/child/types"
)

func (suite *KeeperTestSuite) TestParams() {
	// suite setup initializes genesis
	expParams := types.NewParams(true, 1000, "", "", "0") // these are the default params

	params := suite.childChain.App.(*parentApp.App).ChildKeeper.GetParams(suite.childChain.GetContext())
	suite.Require().Equal(expParams, params)

	newParams := types.NewParams(false, 1000, "abc", "def", "0.6")
	suite.childChain.App.(*parentApp.App).ChildKeeper.SetParams(suite.childChain.GetContext(), newParams)
	params = suite.childChain.App.(*parentApp.App).ChildKeeper.GetParams(suite.childChain.GetContext())
	suite.Require().Equal(newParams, params)

	suite.childChain.App.(*parentApp.App).ChildKeeper.
		SetBlocksPerDistributionTransmission(suite.childChain.GetContext(), 10)
	gotBPDT := suite.childChain.App.(*parentApp.App).ChildKeeper.
		GetBlocksPerDistributionTransmission(suite.childChain.GetContext())
	suite.Require().Equal(gotBPDT, int64(10))

	suite.childChain.App.(*parentApp.App).ChildKeeper.
		SetDistributionTransmissionChannel(suite.childChain.GetContext(), "foobarbaz")
	gotChan := suite.childChain.App.(*parentApp.App).ChildKeeper.
		GetDistributionTransmissionChannel(suite.childChain.GetContext())
	suite.Require().Equal(gotChan, "foobarbaz")

	suite.childChain.App.(*parentApp.App).ChildKeeper.
		SetProviderFeePoolAddrStr(suite.childChain.GetContext(), "foobar")
	gotAddr := suite.childChain.App.(*parentApp.App).ChildKeeper.
		GetProviderFeePoolAddrStr(suite.childChain.GetContext())
	suite.Require().Equal(gotAddr, "foobar")

	suite.childChain.App.(*parentApp.App).ChildKeeper.
		SetConsumerRedistributeFrac(suite.childChain.GetContext(), "0.75")
	gotFrac := suite.childChain.App.(*parentApp.App).ChildKeeper.
		GetConsumerRedistributeFrac(suite.childChain.GetContext())
	suite.Require().Equal(gotFrac, "0.75")
}
