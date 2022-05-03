package keeper_test

import (
	"time"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	commitmenttypes "github.com/cosmos/ibc-go/v3/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	"github.com/cosmos/interchain-security/app"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
)

func (suite *KeeperTestSuite) TestParams() {
	expParams := types.DefaultParams()

	params := suite.providerChain.App.(*app.App).ProviderKeeper.GetParams(suite.providerChain.GetContext())
	suite.Require().Equal(expParams, params)

	newParams := types.NewParams(ibctmtypes.NewClientState("", ibctmtypes.DefaultTrustLevel, 0, 0,
		time.Second*40, clienttypes.Height{}, commitmenttypes.GetSDKSpecs(), []string{"ibc", "upgradedIBCState"}, true, false))
	suite.providerChain.App.(*app.App).ProviderKeeper.SetParams(suite.providerChain.GetContext(), newParams)
	params = suite.providerChain.App.(*app.App).ProviderKeeper.GetParams(suite.providerChain.GetContext())
	suite.Require().Equal(newParams, params)
}
