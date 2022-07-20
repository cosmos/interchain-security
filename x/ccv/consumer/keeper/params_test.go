package keeper_test

import (
	"github.com/cosmos/interchain-security/testutil/simapp"
	"github.com/cosmos/interchain-security/x/ccv/consumer/types"
)

func (suite *KeeperTestSuite) TestParams() {
	// suite setup initializes genesis
	expParams := types.NewParams(true, 1000, "", "") // these are the default params

	params := simapp.GetConsumerKeeper(suite.consumerChain.App).GetParams(suite.consumerChain.GetContext())
	suite.Require().Equal(expParams, params)

	newParams := types.NewParams(false, 1000, "abc", "def")
	simapp.GetConsumerKeeper(suite.consumerChain.App).SetParams(suite.consumerChain.GetContext(), newParams)
	params = simapp.GetConsumerKeeper(suite.consumerChain.App).GetParams(suite.consumerChain.GetContext())
	suite.Require().Equal(newParams, params)

	simapp.GetConsumerKeeper(suite.consumerChain.App).
		SetBlocksPerDistributionTransmission(suite.consumerChain.GetContext(), 10)
	gotBPDT := simapp.GetConsumerKeeper(suite.consumerChain.App).
		GetBlocksPerDistributionTransmission(suite.consumerChain.GetContext())
	suite.Require().Equal(gotBPDT, int64(10))

	simapp.GetConsumerKeeper(suite.consumerChain.App).
		SetDistributionTransmissionChannel(suite.consumerChain.GetContext(), "foobarbaz")
	gotChan := simapp.GetConsumerKeeper(suite.consumerChain.App).
		GetDistributionTransmissionChannel(suite.consumerChain.GetContext())
	suite.Require().Equal(gotChan, "foobarbaz")

	simapp.GetConsumerKeeper(suite.consumerChain.App).
		SetProviderFeePoolAddrStr(suite.consumerChain.GetContext(), "foobar")
	gotAddr := simapp.GetConsumerKeeper(suite.consumerChain.App).
		GetProviderFeePoolAddrStr(suite.consumerChain.GetContext())
	suite.Require().Equal(gotAddr, "foobar")
}
