package provider_test

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	distributiontypes "github.com/cosmos/cosmos-sdk/x/distribution/types"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"

	"testing"
	"time"

	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	"github.com/cosmos/interchain-security/x/ccv/provider"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
)

// TestConsumerChainProposalHandler tests the highest level handler for proposals concerning both
// creating and stopping consumer chains.
func TestConsumerChainProposalHandler(t *testing.T) {

	// Snapshot times asserted in tests
	now := time.Now().UTC()
	hourFromNow := now.Add(time.Hour).UTC()

	testCases := []struct {
		name                     string
		content                  govtypes.Content
		blockTime                time.Time
		expValidConsumerAddition bool
		expValidConsumerRemoval  bool
	}{
		{
			name: "valid consumer addition proposal",
			content: types.NewConsumerAdditionProposal(
				"title", "description", "chainID",
				clienttypes.NewHeight(2, 3), []byte("gen_hash"), []byte("bin_hash"), now),
			blockTime:                hourFromNow, // ctx blocktime is after proposal's spawn time
			expValidConsumerAddition: true,
		},
		{
			name: "valid consumer removal proposal",
			content: types.NewConsumerRemovalProposal(
				"title", "description", "chainID", now),
			blockTime:               hourFromNow,
			expValidConsumerRemoval: true,
		},
		{
			name:      "nil proposal",
			content:   nil,
			blockTime: hourFromNow,
		},
		{
			name: "unsupported proposal type",
			content: distributiontypes.NewCommunityPoolSpendProposal(
				"title", "desc", []byte{},
				sdk.NewCoins(sdk.NewCoin("communityfunds", sdk.NewInt(10)))),
		},
	}

	for _, tc := range testCases {

		// Setup
		keeperParams := testkeeper.NewInMemKeeperParams(t)
		providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, keeperParams)
		providerKeeper.SetParams(ctx, providertypes.DefaultParams())
		ctx = ctx.WithBlockTime(tc.blockTime)

		// Mock expectations depending on expected outcome
		if tc.expValidConsumerAddition {
			gomock.InOrder(testkeeper.GetMocksForCreateConsumerClient(ctx, &mocks, "chainID", clienttypes.NewHeight(2, 3))...)
		}
		if tc.expValidConsumerRemoval {
			testkeeper.SetupForStoppingConsumerChain(t, ctx, &providerKeeper, mocks)
		}

		// Execution
		proposalHandler := provider.NewConsumerChainProposalHandler(providerKeeper)
		err := proposalHandler(ctx, tc.content)

		if tc.expValidConsumerAddition || tc.expValidConsumerRemoval {
			require.NoError(t, err)
		} else {
			require.Error(t, err)
		}
		ctrl.Finish()
	}
}
