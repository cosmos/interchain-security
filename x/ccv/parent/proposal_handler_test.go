package parent_test

import (
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	distributiontypes "github.com/cosmos/cosmos-sdk/x/distribution/types"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"
	appProvider "github.com/cosmos/interchain-security/app_provider"
	"github.com/cosmos/interchain-security/x/ccv/parent"
	"github.com/cosmos/interchain-security/x/ccv/parent/types"
)

func (suite *ParentTestSuite) TestCreateChildChainProposalHandler() {
	var (
		ctx     sdk.Context
		content govtypes.Content
		err     error
	)

	testCases := []struct {
		name     string
		malleate func(*ParentTestSuite)
		expPass  bool
	}{
		{
			"valid create childchain proposal", func(suite *ParentTestSuite) {
				initialHeight := clienttypes.NewHeight(2, 3)
				// ctx blocktime is after proposal's spawn time
				ctx = suite.parentChain.GetContext().WithBlockTime(time.Now().Add(time.Hour))
				content, err = types.NewCreateChildChainProposal("title", "description", "chainID", initialHeight, []byte("gen_hash"), []byte("bin_hash"), time.Now())
				suite.Require().NoError(err)
			}, true,
		},
		{
			"nil proposal", func(suite *ParentTestSuite) {
				ctx = suite.parentChain.GetContext()
				content = nil
			}, false,
		},
		{
			"unsupported proposal type", func(suite *ParentTestSuite) {
				ctx = suite.parentChain.GetContext()
				content = distributiontypes.NewCommunityPoolSpendProposal(ibctesting.Title, ibctesting.Description, suite.parentChain.SenderAccount.GetAddress(), sdk.NewCoins(sdk.NewCoin("communityfunds", sdk.NewInt(10))))
			}, false,
		},
	}

	for _, tc := range testCases {
		tc := tc

		suite.Run(tc.name, func() {
			suite.SetupTest() // reset

			tc.malleate(suite)

			proposalHandler := parent.NewCreateChildChainHandler(suite.parentChain.App.(*appProvider.App).ParentKeeper)

			err = proposalHandler(ctx, content)

			if tc.expPass {
				suite.Require().NoError(err)
			} else {
				suite.Require().Error(err)
			}
		})
	}
}
