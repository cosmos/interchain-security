package provider_test

import (
	"testing"

	capabilitytypes "github.com/cosmos/cosmos-sdk/x/capability/types"
	host "github.com/cosmos/ibc-go/v3/modules/core/24-host"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	"github.com/cosmos/interchain-security/x/ccv/provider"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"

	"github.com/golang/mock/gomock"
)

// Tests the provider's InitGenesis implementation against the spec.
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-initg1
// Spec tag: [CCV-PCF-INITG.1]
//
// Note: Genesis validation for the provider is tested in TestValidateGenesisState
func TestInitGenesis(t *testing.T) {

	type testCase struct {
		name string
		// Whether port capability is already bound to the CCV provider module
		isBound bool
		// Provider's storage of consumer state to test against
		consumerStates []types.ConsumerState
		// Error returned from ClaimCapability during port binding, default: nil
		errFromClaimCap error
		// Whether method call should panic, default: false
		expPanic bool
	}

	tests := []testCase{
		{
			name:           "already bound port, no consumer states",
			isBound:        true,
			consumerStates: []types.ConsumerState{},
		},
		{
			name:           "no bound port, no consumer states",
			isBound:        false,
			consumerStates: []types.ConsumerState{},
		},
		{
			name:    "no bound port, multiple consumer states",
			isBound: false,
			consumerStates: []types.ConsumerState{
				{
					ChainId:   "chainId1",
					ChannelId: "channelIdToChain1",
				},
				{
					ChainId:   "chainId2",
					ChannelId: "channelIdToChain2",
				},
				{
					ChainId:   "chainId3",
					ChannelId: "channelIdToChain3",
				},
			},
		},
		{
			name:    "already bound port, one consumer state",
			isBound: true,
			consumerStates: []types.ConsumerState{
				{
					ChainId:   "chainId77",
					ChannelId: "channelIdToChain77",
				},
			},
		},
		{
			name:    "capability not owned, method should panic",
			isBound: false,
			consumerStates: []types.ConsumerState{
				{
					ChainId:   "chainId77",
					ChannelId: "channelIdToChain77",
				},
			},
			errFromClaimCap: capabilitytypes.ErrCapabilityNotOwned,
			expPanic:        true,
		},
	}

	for _, tc := range tests {
		//
		// Setup
		//
		keeperParams := testkeeper.NewInMemKeeperParams(t)
		providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, keeperParams)

		appModule := provider.NewAppModule(&providerKeeper)
		genState := types.NewGenesisState(
			providerKeeper.GetValidatorSetUpdateId(ctx),
			nil,
			tc.consumerStates,
			nil,
			nil,
			nil,
			nil, types.DefaultParams(),
		)

		cdc := keeperParams.Cdc
		jsonBytes := cdc.MustMarshalJSON(genState)

		//
		// Assert mocked logic before method executes
		//
		orderedCalls := []*gomock.Call{
			mocks.MockScopedKeeper.EXPECT().GetCapability(
				ctx, host.PortPath(ccv.ProviderPortID),
			).Return(
				&capabilitytypes.Capability{},
				tc.isBound, // Capability is returned successfully if port capability is already bound to this module.
			),
		}

		// If port capability is not already bound, port will be bound and capability claimed.
		if !tc.isBound {
			dummyCap := &capabilitytypes.Capability{}

			orderedCalls = append(orderedCalls,
				mocks.MockPortKeeper.EXPECT().BindPort(ctx, ccv.ProviderPortID).Return(dummyCap),
				mocks.MockScopedKeeper.EXPECT().ClaimCapability(
					ctx, dummyCap, host.PortPath(ccv.ProviderPortID)).Return(tc.errFromClaimCap),
			)
		}

		gomock.InOrder(orderedCalls...)

		//
		// Execute method, then assert expected results
		//
		if tc.expPanic {
			require.Panics(t, assert.PanicTestFunc(func() {
				appModule.InitGenesis(ctx, cdc, jsonBytes)
			}), tc.name)
			continue // Nothing else to verify
		}

		valUpdates := appModule.InitGenesis(ctx, cdc, jsonBytes)

		numStatesCounted := 0
		for _, state := range tc.consumerStates {
			numStatesCounted += 1
			channelID, found := providerKeeper.GetChainToChannel(ctx, state.ChainId)
			require.True(t, found)
			require.Equal(t, state.ChannelId, channelID)

			chainID, found := providerKeeper.GetChannelToChain(ctx, state.ChannelId)
			require.True(t, found)
			require.Equal(t, state.ChainId, chainID)
		}
		require.Equal(t, len(tc.consumerStates), numStatesCounted)

		require.Empty(t, valUpdates, "InitGenesis should return no validator updates")

		ctrl.Finish()
	}
}
