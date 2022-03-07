package keeper_test

import (
	"github.com/cosmos/interchain-security/app"
)

// TestValidatorDowntime tests that the slashing hooks
// are registred and triggered when a validator has downtime
func (suite *KeeperTestSuite) TestShouldTransmit() {
	// initial setup
	ap := suite.childChain.App.(*app.App)
	ctx := suite.childChain.GetContext()
	k := ap.ChildKeeper
	_ = k

	// make sure we're starting at height 4 (some blocks commited during setup)
	suite.Require().Equal(int64(4), ctx.BlockHeight())

	// get last transmission
	ltbh, err := k.GetLastTransmissionBlockHeight(ctx)
	suite.Require().NoError(err)
	suite.Require().Equal(int64(0), ltbh.Height)

	//k.SetBlocksPerDistributionTransmission(ctx, 10)
	//store.Set(types.LastDistributionTransmissionKey, 10)

	//st := k.shouldTransmit(ctx)
	//suite.Require().True(st)

}
