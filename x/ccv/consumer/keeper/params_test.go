package keeper_test

import (
	"github.com/cosmos/interchain-security/app"
	"github.com/cosmos/interchain-security/x/ccv/consumer/types"
)

func (suite *KeeperTestSuite) TestParams() {
	// suite setup initializes genesis
	expParams := types.NewParams(true, 1000, "", "", "0") // these are the default params

	params := suite.consumerChain.App.(*app.App).ConsumerKeeper.GetParams(suite.consumerChain.GetContext())
	suite.Require().Equal(expParams, params)

	newParams := types.NewParams(false, 1000, "abc", "def", "0.6")
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

	suite.consumerChain.App.(*app.App).ConsumerKeeper.
		SetConsumerRedistributeFrac(suite.consumerChain.GetContext(), "0.75")
	gotFrac := suite.consumerChain.App.(*app.App).ConsumerKeeper.
		GetConsumerRedistributeFrac(suite.consumerChain.GetContext())
	suite.Require().Equal(gotFrac, "0.75")
}
