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
}
