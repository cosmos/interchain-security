package keeper_test

import (
	"testing"
	"time"

	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"

	sdk "github.com/cosmos/cosmos-sdk/types"

	testkeeper "github.com/cosmos/interchain-security/v4/testutil/keeper"
	providerkeeper "github.com/cosmos/interchain-security/v4/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
)

//
// Initialization sub-protocol related tests of proposal.go
//

// Tests the HandleConsumerAdditionProposal method against the SpawnConsumerChainProposalHandler spec.
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-hcaprop1
// Spec tag: [CCV-PCF-HCAPROP.1]
func TestHandleLegacyConsumerAdditionProposal(t *testing.T) {
	type testCase struct {
		description string
		malleate    func(ctx sdk.Context, k providerkeeper.Keeper, chainID string)
		prop        *providertypes.ConsumerAdditionProposal
		// Time when prop is handled
		blockTime time.Time
		// Whether it's expected that the proposal is successfully verified
		// and appended to the pending proposals
		expAppendProp bool
	}

	// Snapshot times asserted in tests
	now := time.Now().UTC()

	tests := []testCase{
		{
			description: "expect to append valid proposal",
			malleate:    func(ctx sdk.Context, k providerkeeper.Keeper, chainID string) {},
			prop: providertypes.NewConsumerAdditionProposal(
				"title",
				"description",
				"chainID",
				clienttypes.NewHeight(2, 3),
				[]byte("gen_hash"),
				[]byte("bin_hash"),
				now, // Spawn time
				"0.75",
				10,
				"",
				10000,
				100000000000,
				100000000000,
				100000000000,
			).(*providertypes.ConsumerAdditionProposal),
			blockTime:     now,
			expAppendProp: true,
		},
		{
			description: "expect to not append invalid proposal using an already existing chain id",
			malleate: func(ctx sdk.Context, k providerkeeper.Keeper, chainID string) {
				k.SetConsumerClientId(ctx, chainID, "anyClientId")
			},

			prop: providertypes.NewConsumerAdditionProposal(
				"title",
				"description",
				"chainID",
				clienttypes.NewHeight(2, 3),
				[]byte("gen_hash"),
				[]byte("bin_hash"),
				now,
				"0.75",
				10,
				"",
				10000,
				100000000000,
				100000000000,
				100000000000,
			).(*providertypes.ConsumerAdditionProposal),
			blockTime:     now,
			expAppendProp: false,
		},
	}

	for _, tc := range tests {
		// Common setup
		keeperParams := testkeeper.NewInMemKeeperParams(t)
		providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, keeperParams)
		providerKeeper.SetParams(ctx, providertypes.DefaultParams())
		ctx = ctx.WithBlockTime(tc.blockTime)

		if tc.expAppendProp {
			// Mock calls are only asserted if we expect a client to be created.
			gomock.InOrder(
				testkeeper.GetMocksForCreateConsumerClient(ctx, &mocks, tc.prop.ChainId, clienttypes.NewHeight(2, 3))...,
			)
		}

		tc.malleate(ctx, providerKeeper, tc.prop.ChainId)

		err := providerKeeper.HandleLegacyConsumerAdditionProposal(ctx, tc.prop)

		if tc.expAppendProp {
			require.NoError(t, err)
			// check that prop was added to the stored pending props
			gotProposal, found := providerKeeper.GetPendingConsumerAdditionProp(ctx, tc.prop.SpawnTime, tc.prop.ChainId)
			require.True(t, found)
			require.Equal(t, *tc.prop, gotProposal)
		} else {
			require.Error(t, err)
			// check that prop wasn't added to the stored pending props
			_, found := providerKeeper.GetPendingConsumerAdditionProp(ctx, tc.prop.SpawnTime, tc.prop.ChainId)
			require.False(t, found)
		}

		ctrl.Finish()
	}
}

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

		// chainID of the consumer chain
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
				"chainID",
				now,
			).(*providertypes.ConsumerRemovalProposal),
			blockTime:     hourAfterNow, // After stop time.
			expAppendProp: true,
			chainId:       "chainID",
		},
		{
			description: "valid proposal - stop_time in the past",
			setupMocks: func(ctx sdk.Context, k providerkeeper.Keeper, chainID string) {
				k.SetConsumerClientId(ctx, chainID, "ClientID")
			},
			prop: providertypes.NewConsumerRemovalProposal(
				"title",
				"description",
				"chainID",
				hourBeforeNow,
			).(*providertypes.ConsumerRemovalProposal),
			blockTime:     hourAfterNow, // After stop time.
			expAppendProp: true,
			chainId:       "chainID",
		},
		{
			description: "valid proposal - before stop_time in the future",
			setupMocks: func(ctx sdk.Context, k providerkeeper.Keeper, chainID string) {
				k.SetConsumerClientId(ctx, chainID, "ClientID")
			},
			prop: providertypes.NewConsumerRemovalProposal(
				"title",
				"description",
				"chainID",
				hourAfterNow,
			).(*providertypes.ConsumerRemovalProposal),
			blockTime:     now,
			expAppendProp: true,
			chainId:       "chainID",
		},
		{
			description: "rejected valid proposal - consumer chain does not exist",
			setupMocks:  func(ctx sdk.Context, k providerkeeper.Keeper, chainID string) {},
			prop: providertypes.NewConsumerRemovalProposal(
				"title",
				"description",
				"chainID-2",
				hourAfterNow,
			).(*providertypes.ConsumerRemovalProposal),
			blockTime:     hourAfterNow, // After stop time.
			expAppendProp: false,
			chainId:       "chainID-2",
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
			testkeeper.SetupForStoppingConsumerChain(t, ctx, &providerKeeper, mocks)

			// assert mocks for expected calls to `StopConsumerChain` when closing the underlying channel
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
			_, found = providerKeeper.GetChainToChannel(ctx, tc.chainId)
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
