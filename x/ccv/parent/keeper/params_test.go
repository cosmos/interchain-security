package keeper_test

import (
	"time"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	commitmenttypes "github.com/cosmos/ibc-go/v3/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	parentApp "github.com/cosmos/interchain-security/app_parent"
	"github.com/cosmos/interchain-security/x/ccv/parent/types"
)

func (suite *KeeperTestSuite) TestParams() {
	expParams := types.DefaultParams()

	params := suite.parentChain.App.(*parentApp.App).ParentKeeper.GetParams(suite.parentChain.GetContext())
	suite.Require().Equal(expParams, params)

	newParams := types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
		time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}, true, false))
	suite.parentChain.App.(*parentApp.App).ParentKeeper.SetParams(suite.parentChain.GetContext(), newParams)
	params = suite.parentChain.App.(*parentApp.App).ParentKeeper.GetParams(suite.parentChain.GetContext())
	suite.Require().Equal(newParams, params)
}
