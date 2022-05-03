package provider_test

import (
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	distributiontypes "github.com/cosmos/cosmos-sdk/x/distribution/types"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"
	"github.com/cosmos/interchain-security/app"
	"github.com/cosmos/interchain-security/x/ccv/provider"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
)

func (suite *ProviderTestSuite) TestCreateConsumerChainProposalHandler() {
	var (
		ctx     sdk.Context
		content govtypes.Content
		err     error
	)

	testCases := []struct {
		name     string
		malleate func(*ProviderTestSuite)
		expPass  bool
	}{
		{
			"valid create consumerchain proposal", func(suite *ProviderTestSuite) {
				initialHeight := clienttypes.NewHeight(2, 3)
				// ctx blocktime is after proposal's spawn time
				ctx = suite.providerChain.GetContext().WithBlockTime(time.Now().Add(time.Hour))
				content, err = types.NewCreateConsumerChainProposal("title", "description", "chainID", initialHeight, []byte("gen_hash"), []byte("bin_hash"), time.Now())
				suite.Require().NoError(err)
			}, true,
		},
		{
			"nil proposal", func(suite *ProviderTestSuite) {
				ctx = suite.providerChain.GetContext()
				content = nil
			}, false,
		},
		{
			"unsupported proposal type", func(suite *ProviderTestSuite) {
				ctx = suite.providerChain.GetContext()
				content = distributiontypes.NewCommunityPoolSpendProposal(ibctesting.Title, ibctesting.Description, suite.providerChain.SenderAccount.GetAddress(), sdk.NewCoins(sdk.NewCoin("communityfunds", sdk.NewInt(10))))
			}, false,
		},
	}

	for _, tc := range testCases {
		tc := tc

		suite.Run(tc.name, func() {
			suite.SetupTest() // reset

			tc.malleate(suite)

			proposalHandler := provider.NewCreateConsumerChainHandler(suite.providerChain.App.(*app.App).ProviderKeeper)

			err = proposalHandler(ctx, content)

			if tc.expPass {
				suite.Require().NoError(err)
			} else {
				suite.Require().Error(err)
			}
		})
	}
}
