package keeper_test

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	app "github.com/cosmos/interchain-security/app/consumer"
	"github.com/cosmos/interchain-security/x/ccv/consumer/types"
)

func (suite *KeeperTestSuite) TestParams() {
	// suite setup initializes genesis
	expParams := types.NewParams(true, 1000, "", "", sdk.NewDecWithPrec(1, 2), sdk.NewDecWithPrec(4, 2)) // these are the default params

	params := suite.consumerChain.App.(*app.App).ConsumerKeeper.GetParams(suite.consumerChain.GetContext())
	suite.Require().Equal(expParams, params)

	newParams := types.NewParams(false, 1000, "abc", "def", sdk.NewDecWithPrec(1, 2), sdk.NewDecWithPrec(4, 2))
	suite.consumerChain.App.(*app.App).ConsumerKeeper.SetParams(suite.consumerChain.GetContext(), newParams)
	params = suite.consumerChain.App.(*app.App).ConsumerKeeper.GetParams(suite.consumerChain.GetContext())
	suite.Require().Equal(newParams, params)

	suite.consumerChain.App.(*app.App).ConsumerKeeper.
		SetBlocksPerDistributionTransmission(suite.consumerChain.GetContext(), 10)
	gotBPDT := suite.consumerChain.App.(*app.App).ConsumerKeeper.
		GetBlocksPerDistributionTransmission(suite.consumerChain.GetContext())
	suite.Require().Equal(gotBPDT, int64(10))

	suite.consumerChain.App.(*app.App).ConsumerKeeper.
		SetDistributionTransmissionChannel(suite.consumerChain.GetContext(), "foobarbaz")
	gotChan := suite.consumerChain.App.(*app.App).ConsumerKeeper.
		GetDistributionTransmissionChannel(suite.consumerChain.GetContext())
	suite.Require().Equal(gotChan, "foobarbaz")

	suite.consumerChain.App.(*app.App).ConsumerKeeper.
		SetProviderFeePoolAddrStr(suite.consumerChain.GetContext(), "foobar")
	gotAddr := suite.consumerChain.App.(*app.App).ConsumerKeeper.
		GetProviderFeePoolAddrStr(suite.consumerChain.GetContext())
	suite.Require().Equal(gotAddr, "foobar")
}
