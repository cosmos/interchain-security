package keeper_test

import (
	"testing"
	"time"

	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"

	sdk "github.com/cosmos/cosmos-sdk/types"
	testkeeper "github.com/cosmos/interchain-security/v5/testutil/keeper"
	providerkeeper "github.com/cosmos/interchain-security/v5/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
)

//
// Initialization sub-protocol related tests of proposal.go
//

// TestHandleConsumerRemovalProposal tests HandleConsumerRemovalProposal against its corresponding spec method.
//
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-hcrprop1
// Spec tag: [CCV-PCF-HCRPROP.1]
func TestHandleLegacyConsumerRemovalProposal(t *testing.T) {
	type testCase struct {
		description string
		setupMocks  func(ctx sdk.Context, k providerkeeper.Keeper, chainID string)

		// Consumer removal proposal to handle
		prop *providertypes.ConsumerRemovalProposal
		// Time when prop is handled
		blockTime time.Time
		// Whether it's expected that the proposal is successfully verified
		// and appended to the pending proposals
		expAppendProp bool

		// consumerId of the consumer chain
		// tests need to check that the CCV channel is not closed prematurely
		chainId string
	}

	// Snapshot times asserted in tests
	now := time.Now().UTC()
	hourAfterNow := now.Add(time.Hour).UTC()
	hourBeforeNow := now.Add(-time.Hour).UTC()

	tests := []testCase{
		{
			description: "valid proposal",
			setupMocks: func(ctx sdk.Context, k providerkeeper.Keeper, chainID string) {
				k.SetConsumerClientId(ctx, chainID, "ClientID")
			},
			prop: providertypes.NewConsumerRemovalProposal(
				"title",
				"description",
				"consumerId",
				now,
			).(*providertypes.ConsumerRemovalProposal),
			blockTime:     hourAfterNow, // After stop time.
			expAppendProp: true,
			chainId:       "consumerId",
		},
		{
			description: "valid proposal - stop_time in the past",
			setupMocks: func(ctx sdk.Context, k providerkeeper.Keeper, chainID string) {
				k.SetConsumerClientId(ctx, chainID, "ClientID")
			},
			prop: providertypes.NewConsumerRemovalProposal(
				"title",
				"description",
				"consumerId",
				hourBeforeNow,
			).(*providertypes.ConsumerRemovalProposal),
			blockTime:     hourAfterNow, // After stop time.
			expAppendProp: true,
			chainId:       "consumerId",
		},
		{
			description: "valid proposal - before stop_time in the future",
			setupMocks: func(ctx sdk.Context, k providerkeeper.Keeper, chainID string) {
				k.SetConsumerClientId(ctx, chainID, "ClientID")
			},
			prop: providertypes.NewConsumerRemovalProposal(
				"title",
				"description",
				"consumerId",
				hourAfterNow,
			).(*providertypes.ConsumerRemovalProposal),
			blockTime:     now,
			expAppendProp: true,
			chainId:       "consumerId",
		},
		{
			description: "rejected valid proposal - consumer chain does not exist",
			setupMocks:  func(ctx sdk.Context, k providerkeeper.Keeper, chainID string) {},
			prop: providertypes.NewConsumerRemovalProposal(
				"title",
				"description",
				"consumerId-2",
				hourAfterNow,
			).(*providertypes.ConsumerRemovalProposal),
			blockTime:     hourAfterNow, // After stop time.
			expAppendProp: false,
			chainId:       "consumerId-2",
		},
	}

	for _, tc := range tests {

		// Common setup
		keeperParams := testkeeper.NewInMemKeeperParams(t)
		providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, keeperParams)
		providerKeeper.SetParams(ctx, providertypes.DefaultParams())
		ctx = ctx.WithBlockTime(tc.blockTime)

		// Mock expectations and setup for stopping the consumer chain, if applicable
		// Note: when expAppendProp is false, no mocks are setup,
		// meaning no external keeper methods are allowed to be called.
		if tc.expAppendProp {
			testkeeper.SetupForStoppingConsumerChain(t, ctx, &providerKeeper, mocks, tc.prop.ChainId)
			// Valid client creation is asserted with mock expectations here
			gomock.InOrder(testkeeper.GetMocksForStopConsumerChainWithCloseChannel(ctx, &mocks)...)
		}

		tc.setupMocks(ctx, providerKeeper, tc.prop.ChainId)

		err := providerKeeper.HandleLegacyConsumerRemovalProposal(ctx, tc.prop)

		if tc.expAppendProp {
			require.NoError(t, err)

			// Proposal should be stored as pending
			found := providerKeeper.PendingConsumerRemovalPropExists(ctx, tc.prop.ChainId, tc.prop.StopTime)
			require.True(t, found)

			// confirm that the channel was not closed
			_, found = providerKeeper.GetConsumerIdToChannelId(ctx, tc.chainId)
			require.True(t, found)
		} else {
			require.Error(t, err)

			// Expect no pending proposal to exist
			found := providerKeeper.PendingConsumerRemovalPropExists(ctx, tc.prop.ChainId, tc.prop.StopTime)
			require.False(t, found)
		}

		// Assert mock calls from setup function
		ctrl.Finish()
	}
}
