package keeper_test

import (
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"

	clienttypes "github.com/cosmos/ibc-go/modules/core/02-client/types"
	"github.com/cosmos/interchain-security/app"
	"github.com/cosmos/interchain-security/x/ccv/parent/types"
)

func (suite *KeeperTestSuite) TestCreateChildChainProposal() {
	var (
		ctx      sdk.Context
		proposal *types.CreateChildChainProposal
		ok       bool
	)

	chainID := "chainID"
	initialHeight := clienttypes.NewHeight(2, 3)

	testCases := []struct {
		name         string
		malleate     func(*KeeperTestSuite)
		expPass      bool
		spawnReached bool
	}{
		{
			"valid create child chain proposal: spawn time reached", func(suite *KeeperTestSuite) {
				// ctx blocktime is after proposal's spawn time
				ctx = suite.parentChain.GetContext().WithBlockTime(time.Now().Add(time.Hour))
				content, err := types.NewCreateChildChainProposal("title", "description", chainID, initialHeight, []byte("gen_hash"), []byte("bin_hash"), time.Now())
				suite.Require().NoError(err)
				proposal, ok = content.(*types.CreateChildChainProposal)
				suite.Require().True(ok)
			}, true, true,
		},
		{
			"valid proposal: spawn time has not yet been reached", func(suite *KeeperTestSuite) {
				// ctx blocktime is before proposal's spawn time
				ctx = suite.parentChain.GetContext().WithBlockTime(time.Now())
				content, err := types.NewCreateChildChainProposal("title", "description", chainID, initialHeight, []byte("gen_hash"), []byte("bin_hash"), time.Now().Add(time.Hour))
				suite.Require().NoError(err)
				proposal, ok = content.(*types.CreateChildChainProposal)
				suite.Require().True(ok)
			}, true, false,
		},
	}

	for _, tc := range testCases {
		tc := tc

		suite.Run(tc.name, func() {
			suite.SetupTest()

			tc.malleate(suite)

			err := suite.parentChain.App.(*app.App).ParentKeeper.CreateChildChainProposal(ctx, proposal)
			if tc.expPass {
				suite.Require().NoError(err, "error returned on valid case")
				if tc.spawnReached {
					clientId := suite.parentChain.App.(*app.App).ParentKeeper.GetChildClient(ctx, chainID)
					suite.Require().NotEqual("", clientId, "child client was not created after spawn time reached")
				} else {
					gotHeight := suite.parentChain.App.(*app.App).ParentKeeper.GetPendingClientInfo(ctx, proposal.SpawnTime, chainID)
					suite.Require().Equal(initialHeight, gotHeight, "pending client not equal to clientstate in proposal")
				}
			} else {
				suite.Require().Error(err, "did not return error on invalid case")
			}
		})
	}
}
