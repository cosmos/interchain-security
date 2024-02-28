package provider_test

import (
	"testing"
	"time"

	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"

	sdk "github.com/cosmos/cosmos-sdk/types"
	distributiontypes "github.com/cosmos/cosmos-sdk/x/distribution/types"
	govv1beta1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1beta1"

	testkeeper "github.com/cosmos/interchain-security/v4/testutil/keeper"
	"github.com/cosmos/interchain-security/v4/x/ccv/provider"
	providertypes "github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
)

// TestProviderProposalHandler tests the highest level handler for proposals
// concerning creating, stopping consumer chains and changing reward denom.
func TestProviderProposalHandler(t *testing.T) {
	// Snapshot times asserted in tests
	now := time.Now().UTC()
	hourFromNow := now.Add(time.Hour).UTC()

	testCases := []struct {
		name                      string
		content                   govv1beta1.Content
		blockTime                 time.Time
		expValidConsumerAddition  bool
		expValidConsumerRemoval   bool
		expValidChangeRewardDenom bool
	}{
		{
			name: "valid consumer addition proposal",
			content: providertypes.NewConsumerAdditionProposal(
				"title", "description", "chainID",
				clienttypes.NewHeight(2, 3), []byte("gen_hash"), []byte("bin_hash"), now,
				"0.75",
				10,
				"",
				10000,
				100000000000,
				100000000000,
				100000000000,
			),
			blockTime:                hourFromNow, // ctx blocktime is after proposal's spawn time
			expValidConsumerAddition: true,
		},
		{
			name: "valid consumer removal proposal",
			content: providertypes.NewConsumerRemovalProposal(
				"title", "description", "chainID", now),
			blockTime:               hourFromNow,
			expValidConsumerRemoval: true,
		},
		{
			name: "valid change reward denoms proposal",
			content: providertypes.NewChangeRewardDenomsProposal(
				"title", "description", []string{"denom1"}, []string{"denom2"}),
			blockTime:                 hourFromNow,
			expValidChangeRewardDenom: true,
		},
		{
			name:      "nil proposal",
			content:   nil,
			blockTime: hourFromNow,
		},
		{
			name: "unsupported proposal type",
			// lint rule disabled because this is a test case for an unsupported proposal type
			// nolint:staticcheck
			content: &distributiontypes.CommunityPoolSpendProposal{
				Title:       "title",
				Description: "desc",
				Recipient:   "",
				Amount:      sdk.NewCoins(sdk.NewCoin("communityfunds", sdk.NewInt(10))),
			},
		},
	}

	for _, tc := range testCases {

		// Setup
		keeperParams := testkeeper.NewInMemKeeperParams(t)
		providerKeeper, ctx, _, mocks := testkeeper.GetProviderKeeperAndCtx(t, keeperParams)
		providerKeeper.SetParams(ctx, providertypes.DefaultParams())
		ctx = ctx.WithBlockTime(tc.blockTime)

		// Mock expectations depending on expected outcome
		switch {
		case tc.expValidConsumerAddition:
			gomock.InOrder(testkeeper.GetMocksForCreateConsumerClient(
				ctx, &mocks, "chainID", clienttypes.NewHeight(2, 3),
			)...)

		case tc.expValidConsumerRemoval:
			testkeeper.SetupForStoppingConsumerChain(t, ctx, &providerKeeper, mocks)

			// assert mocks for expected calls to `StopConsumerChain` when closing the underlying channel
			gomock.InOrder(testkeeper.GetMocksForStopConsumerChainWithCloseChannel(ctx, &mocks)...)
		case tc.expValidChangeRewardDenom:
			// Nothing to mock
		}

		// Execution
		proposalHandler := provider.NewProviderProposalHandler(providerKeeper)
		err := proposalHandler(ctx, tc.content)

		if tc.expValidConsumerAddition || tc.expValidConsumerRemoval ||
			tc.expValidChangeRewardDenom {
			require.NoError(t, err)
		} else {
			require.Error(t, err)
		}
	}
}
