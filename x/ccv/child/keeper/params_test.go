package keeper_test

import (
	"github.com/cosmos/interchain-security/app"
	"github.com/cosmos/interchain-security/x/ccv/child/types"
)

func (suite *KeeperTestSuite) TestParams() {
	// suite setup initializes genesis with enabled = true
	expParams := types.NewParams(true)

	params := suite.childChain.App.(*app.App).ChildKeeper.GetParams(suite.childChain.GetContext())
	suite.Require().Equal(expParams, params)

	newParams := types.NewParams(false)
	suite.childChain.App.(*app.App).ChildKeeper.SetParams(suite.childChain.GetContext(), newParams)
	params = suite.childChain.App.(*app.App).ChildKeeper.GetParams(suite.childChain.GetContext())
	suite.Require().Equal(newParams, params)

	suite.childChain.App.(*app.App).ChildKeeper.
		SetBlocksPerDistributionTransmission(suite.childChain.GetContext(), 10)
	gotBPDT := suite.childChain.App.(*app.App).ChildKeeper.
		GetBlocksPerDistributionTransmission(suite.childChain.GetContext())
	suite.Require().Equal(gotBPDT, int64(10))

	suite.childChain.App.(*app.App).ChildKeeper.
		SetProviderFeePoolAddrStr(suite.childChain.GetContext(), "foobar")
	gotAddr := suite.childChain.App.(*app.App).ChildKeeper.
		GetProviderFeePoolAddrStr(suite.childChain.GetContext())
	suite.Require().Equal(gotAddr, "foobar")

	suite.childChain.App.(*app.App).ChildKeeper.
		SetDistributionTransmissionChannel(suite.childChain.GetContext(), "foobarbaz")
	gotChan := suite.childChain.App.(*app.App).ChildKeeper.
		GetDistributionTransmissionChannel(suite.childChain.GetContext())
	suite.Require().Equal(gotChan, "foobarbaz")
}
