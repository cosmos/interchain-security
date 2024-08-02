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
			testkeeper.SetupForStoppingConsumerChain(t, ctx, &providerKeeper, mocks, tc.prop.ConsumerId)
			// Valid client creation is asserted with mock expectations here
			gomock.InOrder(testkeeper.GetMocksForStopConsumerChainWithCloseChannel(ctx, &mocks)...)
		}

		tc.setupMocks(ctx, providerKeeper, tc.prop.ConsumerId)

		err := providerKeeper.HandleLegacyConsumerRemovalProposal(ctx, tc.prop)

		if tc.expAppendProp {
			require.NoError(t, err)

			// Proposal should be stored as pending
			found := providerKeeper.PendingConsumerRemovalPropExists(ctx, tc.prop.ConsumerId, tc.prop.StopTime)
			require.True(t, found)

			// confirm that the channel was not closed
			_, found = providerKeeper.GetConsumerIdToChannelId(ctx, tc.chainId)
			require.True(t, found)
		} else {
			require.Error(t, err)

			// Expect no pending proposal to exist
			found := providerKeeper.PendingConsumerRemovalPropExists(ctx, tc.prop.ConsumerId, tc.prop.StopTime)
			require.False(t, found)
		}

		// Assert mock calls from setup function
		ctrl.Finish()
	}
}

func TestHandleConsumerModificationProposal(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	chainID := "chainID"

	// set up a consumer client, so it seems that "chainID" is running
	providerKeeper.SetConsumerClientId(ctx, "chainID", "clientID")

	// set PSS-related fields to update them later on
	providerKeeper.SetTopN(ctx, chainID, 50)
	providerKeeper.SetValidatorSetCap(ctx, chainID, 10)
	providerKeeper.SetValidatorsPowerCap(ctx, chainID, 34)
	providerKeeper.SetAllowlist(ctx, chainID, providertypes.NewProviderConsAddress([]byte("allowlistedAddr1")))
	providerKeeper.SetAllowlist(ctx, chainID, providertypes.NewProviderConsAddress([]byte("allowlistedAddr2")))
	providerKeeper.SetDenylist(ctx, chainID, providertypes.NewProviderConsAddress([]byte("denylistedAddr1")))
	providerKeeper.SetMinStake(ctx, chainID, 1000)
	providerKeeper.SetInactiveValidatorsAllowed(ctx, chainID, true)

	expectedTopN := uint32(75)
	expectedValidatorsPowerCap := uint32(67)
	expectedValidatorSetCap := uint32(20)
	expectedAllowlistedValidator := "cosmosvalcons1wpex7anfv3jhystyv3eq20r35a"
	expectedDenylistedValidator := "cosmosvalcons1nx7n5uh0ztxsynn4sje6eyq2ud6rc6klc96w39"
	expectedMinStake := uint64(0)
	expectedAllowInactiveValidators := false
	proposal := providertypes.NewConsumerModificationProposal("title", "description", chainID,
		expectedTopN,
		expectedValidatorsPowerCap,
		expectedValidatorSetCap,
		[]string{expectedAllowlistedValidator},
		[]string{expectedDenylistedValidator},
		expectedMinStake,
		expectedAllowInactiveValidators,
	).(*providertypes.ConsumerModificationProposal)

	err := providerKeeper.HandleLegacyConsumerModificationProposal(ctx, proposal)
	require.NoError(t, err)

	actualTopN, _ := providerKeeper.GetTopN(ctx, chainID)
	require.Equal(t, expectedTopN, actualTopN)
	actualValidatorsPowerCap, _ := providerKeeper.GetValidatorsPowerCap(ctx, chainID)
	require.Equal(t, expectedValidatorsPowerCap, actualValidatorsPowerCap)
	actualValidatorSetCap, _ := providerKeeper.GetValidatorSetCap(ctx, chainID)
	require.Equal(t, expectedValidatorSetCap, actualValidatorSetCap)

	allowlistedValidator, err := sdk.ConsAddressFromBech32(expectedAllowlistedValidator)
	require.NoError(t, err)
	require.Equal(t, 1, len(providerKeeper.GetAllowList(ctx, chainID)))
	require.Equal(t, providertypes.NewProviderConsAddress(allowlistedValidator), providerKeeper.GetAllowList(ctx, chainID)[0])

	denylistedValidator, err := sdk.ConsAddressFromBech32(expectedDenylistedValidator)
	require.NoError(t, err)
	require.Equal(t, 1, len(providerKeeper.GetDenyList(ctx, chainID)))
	require.Equal(t, providertypes.NewProviderConsAddress(denylistedValidator), providerKeeper.GetDenyList(ctx, chainID)[0])

	actualMinStake, _ := providerKeeper.GetMinStake(ctx, chainID)
	require.Equal(t, expectedMinStake, actualMinStake)

	actualAllowInactiveValidators := providerKeeper.AllowsInactiveValidators(ctx, chainID)
	require.Equal(t, expectedAllowInactiveValidators, actualAllowInactiveValidators)
}
