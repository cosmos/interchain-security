package provider_test

import (
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	"cosmossdk.io/math"

	sdk "github.com/cosmos/cosmos-sdk/types"
	distributiontypes "github.com/cosmos/cosmos-sdk/x/distribution/types"
	govv1beta1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1beta1"

	testkeeper "github.com/cosmos/interchain-security/v6/testutil/keeper"
	"github.com/cosmos/interchain-security/v6/x/ccv/provider"
	providertypes "github.com/cosmos/interchain-security/v6/x/ccv/provider/types"
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
		expValidConsumerRemoval   bool
		expValidChangeRewardDenom bool
	}{
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
				Amount:      sdk.NewCoins(sdk.NewCoin("communityfunds", math.NewInt(10))),
			},
		},
	}

	for _, tc := range testCases {

		// Setup
		keeperParams := testkeeper.NewInMemKeeperParams(t)
		providerKeeper, ctx, _, _ := testkeeper.GetProviderKeeperAndCtx(t, keeperParams)
		providerKeeper.SetParams(ctx, providertypes.DefaultParams())
		ctx = ctx.WithBlockTime(tc.blockTime)

		// Mock expectations depending on expected outcome
		switch {
		case tc.expValidChangeRewardDenom:
			// Nothing to mock
		}

		// Execution
		proposalHandler := provider.NewProviderProposalHandler(providerKeeper)
		err := proposalHandler(ctx, tc.content)
		if tc.expValidChangeRewardDenom {
			require.NoError(t, err)
		} else {
			require.Error(t, err)
		}
	}
}
