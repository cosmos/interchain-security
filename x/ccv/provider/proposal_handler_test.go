package provider_test

import (
	"testing"
	"time"

	"cosmossdk.io/math"
	sdk "github.com/cosmos/cosmos-sdk/types"
	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"

	distributiontypes "github.com/cosmos/cosmos-sdk/x/distribution/types"
	govv1beta1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1beta1"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	testkeeper "github.com/cosmos/interchain-security/v5/testutil/keeper"
	"github.com/cosmos/interchain-security/v5/x/ccv/provider"
	providertypes "github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
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
		expValidConsumerModif     bool
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
				0,
				0,
				0,
				nil,
				nil,
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
			name: "valid consumer modification proposal",
			content: providertypes.NewConsumerModificationProposal(
				"title", "description", "chainID",
				50,
				100,
				34,
				[]string{"addr1"},
				nil,
			),
			blockTime:             hourFromNow,
			expValidConsumerModif: true,
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
		providerKeeper, ctx, _, mocks := testkeeper.GetProviderKeeperAndCtx(t, keeperParams)
		providerKeeper.SetParams(ctx, providertypes.DefaultParams())
		ctx = ctx.WithBlockTime(tc.blockTime)

		// Mock expectations depending on expected outcome
		switch {
		case tc.expValidConsumerAddition:
			testkeeper.SetupMocksForLastBondedValidatorsExpectation(mocks.MockStakingKeeper, 1, []stakingtypes.Validator{}, []int64{}, 1)
			gomock.InOrder(testkeeper.GetMocksForCreateConsumerClient(
				ctx, &mocks, "chainID", clienttypes.NewHeight(2, 3),
			)...)

		case tc.expValidConsumerRemoval:
			testkeeper.SetupForStoppingConsumerChain(t, ctx, &providerKeeper, mocks)

			// assert mocks for expected calls to `StopConsumerChain` when closing the underlying channel
			gomock.InOrder(testkeeper.GetMocksForStopConsumerChainWithCloseChannel(ctx, &mocks)...)
		case tc.expValidChangeRewardDenom:
			// Nothing to mock

		case tc.expValidConsumerModif:
			// set up a consumer client, so it seems that "chainID" is running
			providerKeeper.SetConsumerClientId(ctx, "chainID", "clientID")
		}

		// Execution
		proposalHandler := provider.NewProviderProposalHandler(providerKeeper)
		err := proposalHandler(ctx, tc.content)

		if tc.expValidConsumerAddition || tc.expValidConsumerRemoval ||
			tc.expValidChangeRewardDenom || tc.expValidConsumerModif {
			require.NoError(t, err)
		} else {
			require.Error(t, err)
		}
	}
}
