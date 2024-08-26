package keeper_test

import (
	"bytes"
	"encoding/json"
	"fmt"
	"sort"
	"testing"
	"time"

	cryptotestutil "github.com/cosmos/interchain-security/v5/testutil/crypto"

	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	"cosmossdk.io/math"
	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
	ibctmtypes "github.com/cosmos/ibc-go/v8/modules/light-clients/07-tendermint"
	_go "github.com/cosmos/ics23/go"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"

	abci "github.com/cometbft/cometbft/abci/types"
	sdk "github.com/cosmos/cosmos-sdk/types"

	testkeeper "github.com/cosmos/interchain-security/v5/testutil/keeper"
	providerkeeper "github.com/cosmos/interchain-security/v5/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v5/x/ccv/types"
)

//
// Initialization sub-protocol related tests of proposal.go
//

// Tests the CreateConsumerClient method against the spec,
// with more granularity than what's covered in TestHandleCreateConsumerChainProposal.
func TestCreateConsumerClient(t *testing.T) {
	type testCase struct {
		description string
		// Any state-mutating setup on keeper and expected mock calls, specific to this test case
		setup func(*providerkeeper.Keeper, sdk.Context, *testkeeper.MockedKeepers)
		// Whether a client should be created
		expClientCreated bool
	}
	tests := []testCase{
		{
			description: "No state mutation, new client should be created",
			setup: func(providerKeeper *providerkeeper.Keeper, ctx sdk.Context, mocks *testkeeper.MockedKeepers) {
				providerKeeper.SetConsumerPhase(ctx, "0", providerkeeper.Initialized)

				// Valid client creation is asserted with mock expectations here
				testkeeper.SetupMocksForLastBondedValidatorsExpectation(mocks.MockStakingKeeper, 0, []stakingtypes.Validator{}, 1) // returns empty validator set
				gomock.InOrder(
					testkeeper.GetMocksForCreateConsumerClient(ctx, mocks, "chainID", clienttypes.NewHeight(4, 5))...,
				)
			},
			expClientCreated: true,
		},
		{
			description: "chain for this consumer id has already launched, and hence client was created, NO new one is created",
			setup: func(providerKeeper *providerkeeper.Keeper, ctx sdk.Context, mocks *testkeeper.MockedKeepers) {
				providerKeeper.SetConsumerPhase(ctx, "0", providerkeeper.Launched)

				// Expect none of the client creation related calls to happen
				mocks.MockStakingKeeper.EXPECT().UnbondingTime(gomock.Any()).Times(0)
				mocks.MockClientKeeper.EXPECT().CreateClient(gomock.Any(), gomock.Any(), gomock.Any()).Times(0)
				mocks.MockClientKeeper.EXPECT().GetSelfConsensusState(gomock.Any(), gomock.Any()).Times(0)
				testkeeper.SetupMocksForLastBondedValidatorsExpectation(mocks.MockStakingKeeper, 0, []stakingtypes.Validator{}, 0) // returns empty validator set
			},
			expClientCreated: false,
		},
	}

	for _, tc := range tests {
		// Common setup
		keeperParams := testkeeper.NewInMemKeeperParams(t)
		providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, keeperParams)
		providerKeeper.SetParams(ctx, providertypes.DefaultParams())

		// Test specific setup
		tc.setup(&providerKeeper, ctx, &mocks)

		// Call method with same arbitrary values as defined above in mock expectations.
		providerKeeper.SetConsumerChainId(ctx, "0", "chainID")
		providerKeeper.SetConsumerMetadata(ctx, "0", testkeeper.GetTestConsumerMetadata())
		providerKeeper.SetConsumerInitializationParameters(ctx, "0", testkeeper.GetTestInitializationParameters())
		providerKeeper.SetConsumerPowerShapingParameters(ctx, "0", testkeeper.GetTestPowerShapingParameters())
		err := providerKeeper.CreateConsumerClient(ctx, "0")

		if tc.expClientCreated {
			require.NoError(t, err)
			testCreatedConsumerClient(t, ctx, providerKeeper, "0", "clientID")
		} else {
			require.Error(t, err)
		}

		// Assert mock calls from setup functions
		ctrl.Finish()
	}
}

// Executes test assertions for a created consumer client.
//
// Note: Separated from TestCreateConsumerClient to also be called from TestCreateConsumerChainProposal.
func testCreatedConsumerClient(t *testing.T,
	ctx sdk.Context, providerKeeper providerkeeper.Keeper, consumerId, expectedClientID string,
) {
	t.Helper()
	// ClientID should be stored.
	clientId, found := providerKeeper.GetConsumerClientId(ctx, consumerId)
	require.True(t, found, "consumer client not found")
	require.Equal(t, expectedClientID, clientId)

	// Only assert that consumer genesis was set,
	// more granular tests on consumer genesis should be defined in TestMakeConsumerGenesis
	_, ok := providerKeeper.GetConsumerGenesis(ctx, consumerId)
	require.True(t, ok)
}

// TestPendingConsumerAdditionPropDeletion tests the getting/setting
// and deletion keeper methods for pending consumer addition props
func TestPendingConsumerAdditionPropDeletion(t *testing.T) {
	testCases := []struct {
		providertypes.ConsumerAdditionProposal
		ExpDeleted bool
	}{
		{
			ConsumerAdditionProposal: providertypes.ConsumerAdditionProposal{ChainId: "0", SpawnTime: time.Now().UTC()},
			ExpDeleted:               true,
		},
		{
			ConsumerAdditionProposal: providertypes.ConsumerAdditionProposal{ChainId: "1", SpawnTime: time.Now().UTC().Add(time.Hour)},
			ExpDeleted:               false,
		},
	}
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	for _, tc := range testCases {
		tc := tc
		providerKeeper.SetPendingConsumerAdditionProp(ctx, &tc.ConsumerAdditionProposal)
	}

	ctx = ctx.WithBlockTime(time.Now().UTC())

	propsToExecute := providerKeeper.GetConsumerAdditionPropsToExecute(ctx)
	// Delete consumer addition proposals, same as what would be done by BeginBlockInit
	providerKeeper.DeletePendingConsumerAdditionProps(ctx, propsToExecute...)
	numDeleted := 0
	for _, tc := range testCases {
		res, found := providerKeeper.GetPendingConsumerAdditionProp(ctx, tc.SpawnTime, tc.ChainId)
		if !tc.ExpDeleted {
			require.True(t, found)
			require.NotEmpty(t, res, "consumer addition proposal was deleted: %s %s", tc.ChainId, tc.SpawnTime.String())
			continue
		}
		require.Empty(t, res, "consumer addition proposal was not deleted %s %s", tc.ChainId, tc.SpawnTime.String())
		require.Equal(t, propsToExecute[numDeleted].ChainId, tc.ChainId)
		numDeleted += 1
	}
}

// TestGetConsumerAdditionPropsToExecute tests that pending consumer addition proposals
// that are ready to execute are accessed in order by timestamp via the iterator
func TestGetConsumerAdditionPropsToExecute(t *testing.T) {
	now := time.Now().UTC()
	sampleProp1 := providertypes.ConsumerAdditionProposal{ChainId: "chain-2", SpawnTime: now}
	sampleProp2 := providertypes.ConsumerAdditionProposal{ChainId: "chain-1", SpawnTime: now.Add(time.Hour)}
	sampleProp3 := providertypes.ConsumerAdditionProposal{ChainId: "chain-4", SpawnTime: now.Add(-time.Hour)}
	sampleProp4 := providertypes.ConsumerAdditionProposal{ChainId: "chain-3", SpawnTime: now}
	sampleProp5 := providertypes.ConsumerAdditionProposal{ChainId: "chain-1", SpawnTime: now.Add(2 * time.Hour)}

	getExpectedOrder := func(props []providertypes.ConsumerAdditionProposal, accessTime time.Time) []providertypes.ConsumerAdditionProposal {
		expectedOrder := []providertypes.ConsumerAdditionProposal{}
		for _, prop := range props {
			if !accessTime.Before(prop.SpawnTime) {
				expectedOrder = append(expectedOrder, prop)
			}
		}
		if len(expectedOrder) == 0 {
			return nil
		}
		// sorting by SpawnTime.UnixNano()
		sort.Slice(expectedOrder, func(i, j int) bool {
			if expectedOrder[i].SpawnTime.UTC() == expectedOrder[j].SpawnTime.UTC() {
				// proposals with same SpawnTime
				return expectedOrder[i].ChainId < expectedOrder[j].ChainId
			}
			return expectedOrder[i].SpawnTime.UTC().Before(expectedOrder[j].SpawnTime.UTC())
		})
		return expectedOrder
	}

	testCases := []struct {
		propSubmitOrder []providertypes.ConsumerAdditionProposal
		accessTime      time.Time
	}{
		{
			propSubmitOrder: []providertypes.ConsumerAdditionProposal{
				sampleProp1, sampleProp2, sampleProp3, sampleProp4, sampleProp5,
			},
			accessTime: now,
		},
		{
			propSubmitOrder: []providertypes.ConsumerAdditionProposal{
				sampleProp3, sampleProp2, sampleProp1, sampleProp5, sampleProp4,
			},
			accessTime: now.Add(time.Hour),
		},
		{
			propSubmitOrder: []providertypes.ConsumerAdditionProposal{
				sampleProp5, sampleProp4, sampleProp3, sampleProp2, sampleProp1,
			},
			accessTime: now.Add(-2 * time.Hour),
		},
		{
			propSubmitOrder: []providertypes.ConsumerAdditionProposal{
				sampleProp5, sampleProp4, sampleProp3, sampleProp2, sampleProp1,
			},
			accessTime: now.Add(3 * time.Hour),
		},
	}

	for _, tc := range testCases {
		providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
		defer ctrl.Finish()

		expectedOrderedProps := getExpectedOrder(tc.propSubmitOrder, tc.accessTime)

		for _, prop := range tc.propSubmitOrder {
			cpProp := prop
			providerKeeper.SetPendingConsumerAdditionProp(ctx, &cpProp)
		}
		propsToExecute := providerKeeper.GetConsumerAdditionPropsToExecute(ctx.WithBlockTime(tc.accessTime))
		require.Equal(t, expectedOrderedProps, propsToExecute)
	}
}

// Test getting both matured and pending consumer addition proposals
func TestGetAllConsumerAdditionProps(t *testing.T) {
	pk, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	now := time.Now().UTC()
	props := []providertypes.ConsumerAdditionProposal{
		{ChainId: "chain-2", SpawnTime: now},
		{ChainId: "chain-1", SpawnTime: now.Add(2 * time.Hour)},
		{ChainId: "chain-4", SpawnTime: now.Add(-time.Hour)},
		{ChainId: "chain-3", SpawnTime: now.Add(4 * time.Hour)},
		{ChainId: "chain-1", SpawnTime: now},
	}
	expectedGetAllOrder := props
	// sorting by SpawnTime.UnixNano()
	sort.Slice(expectedGetAllOrder, func(i, j int) bool {
		tsi := uint64(expectedGetAllOrder[i].SpawnTime.UTC().UnixNano())
		tsj := uint64(expectedGetAllOrder[j].SpawnTime.UTC().UnixNano())
		cmpTimestamps := bytes.Compare(sdk.Uint64ToBigEndian(tsi), sdk.Uint64ToBigEndian(tsj))
		if cmpTimestamps == 0 {
			// proposals with same SpawnTime
			return expectedGetAllOrder[i].ChainId < expectedGetAllOrder[j].ChainId
		}
		return cmpTimestamps == -1
	})

	for _, prop := range props {
		cpProp := prop // bring into loop scope - avoids using iterator pointer instead of value pointer
		pk.SetPendingConsumerAdditionProp(ctx, &cpProp)
	}

	// iterate and check all results are returned in the expected order
	result := pk.GetAllPendingConsumerAdditionProps(ctx.WithBlockTime(now))
	require.Len(t, result, len(props))
	require.Equal(t, expectedGetAllOrder, result)
}

// Tests the StopConsumerChain method against the spec,
// with more granularity than what's covered in TestHandleLegacyConsumerRemovalProposal, or integration tests.
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-stcc1
// Spec tag: [CCV-PCF-STCC.1]
func TestStopConsumerChain(t *testing.T) {
	type testCase struct {
		description string
		// State-mutating setup specific to this test case
		setup func(sdk.Context, *providerkeeper.Keeper, testkeeper.MockedKeepers)
		// Whether we should expect the method to return an error
		expErr bool
	}

	consumerId := "0"

	tests := []testCase{
		{
			description: "proposal dropped, client doesn't exist",
			setup: func(ctx sdk.Context, providerKeeper *providerkeeper.Keeper, mocks testkeeper.MockedKeepers) {
				// No mocks, meaning no external keeper methods are allowed to be called.
			},
			expErr: true,
		},
		{
			description: "valid stop of consumer chain, all mock calls hit",
			setup: func(ctx sdk.Context, providerKeeper *providerkeeper.Keeper, mocks testkeeper.MockedKeepers) {
				testkeeper.SetupForStoppingConsumerChain(t, ctx, providerKeeper, mocks, consumerId)

				// set consumer minimum equivocation height
				providerKeeper.SetEquivocationEvidenceMinHeight(ctx, consumerId, 1)

				// assert mocks for expected calls to `StopConsumerChain` when closing the underlying channel
				gomock.InOrder(testkeeper.GetMocksForStopConsumerChainWithCloseChannel(ctx, &mocks)...)
			},
			expErr: false,
		},
	}

	for _, tc := range tests {

		// Common setup
		keeperParams := testkeeper.NewInMemKeeperParams(t)
		providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, keeperParams)
		providerKeeper.SetParams(ctx, providertypes.DefaultParams())

		// Setup specific to test case
		tc.setup(ctx, &providerKeeper, mocks)

		err := providerKeeper.StopConsumerChain(ctx, consumerId, true)

		if tc.expErr {
			require.Error(t, err, t)
		} else {
			require.NoError(t, err)
		}

		testkeeper.TestProviderStateIsCleanedAfterConsumerChainIsStopped(t, ctx, providerKeeper, consumerId, "channelID")

		ctrl.Finish()
	}
}

// TODO (PERMISSIONLESS)
// WE DO NOT go by order in permissionless (?) DO WE need to?
// TestGetConsumerRemovalPropsToExecute tests that pending consumer removal proposals
// that are ready to execute are accessed in order by timestamp via the iterator
//func TestGetConsumerRemovalPropsToExecute(t *testing.T) {
//	now := time.Now().UTC()
//	sampleProp1 := providertypes.ConsumerRemovalProposal{ConsumerId: "chain-2", StopTime: now}
//	sampleProp2 := providertypes.ConsumerRemovalProposal{ConsumerId: "chain-1", StopTime: now.Add(time.Hour)}
//	sampleProp3 := providertypes.ConsumerRemovalProposal{ConsumerId: "chain-4", StopTime: now.Add(-time.Hour)}
//	sampleProp4 := providertypes.ConsumerRemovalProposal{ConsumerId: "chain-3", StopTime: now}
//	sampleProp5 := providertypes.ConsumerRemovalProposal{ConsumerId: "chain-1", StopTime: now.Add(2 * time.Hour)}
//
//	getExpectedOrder := func(props []providertypes.ConsumerRemovalProposal, accessTime time.Time) []providertypes.ConsumerRemovalProposal {
//		expectedOrder := []providertypes.ConsumerRemovalProposal{}
//		for _, prop := range props {
//			if !accessTime.Before(prop.StopTime) {
//				expectedOrder = append(expectedOrder, prop)
//			}
//		}
//		// sorting by SpawnTime.UnixNano()
//		sort.Slice(expectedOrder, func(i, j int) bool {
//			if expectedOrder[i].StopTime.UTC() == expectedOrder[j].StopTime.UTC() {
//				// proposals with same StopTime
//				return expectedOrder[i].ConsumerId < expectedOrder[j].ConsumerId
//			}
//			return expectedOrder[i].StopTime.UTC().Before(expectedOrder[j].StopTime.UTC())
//		})
//		return expectedOrder
//	}
//
//	testCases := []struct {
//		propSubmitOrder []providertypes.ConsumerRemovalProposal
//		accessTime      time.Time
//	}{
//		{
//			propSubmitOrder: []providertypes.ConsumerRemovalProposal{
//				sampleProp1, sampleProp2, sampleProp3, sampleProp4, sampleProp5,
//			},
//			accessTime: now,
//		},
//		{
//			propSubmitOrder: []providertypes.ConsumerRemovalProposal{
//				sampleProp3, sampleProp2, sampleProp1, sampleProp5, sampleProp4,
//			},
//			accessTime: now.Add(time.Hour),
//		},
//		{
//			propSubmitOrder: []providertypes.ConsumerRemovalProposal{
//				sampleProp5, sampleProp4, sampleProp3, sampleProp2, sampleProp1,
//			},
//			accessTime: now.Add(-2 * time.Hour),
//		},
//		{
//			propSubmitOrder: []providertypes.ConsumerRemovalProposal{
//				sampleProp5, sampleProp4, sampleProp3, sampleProp2, sampleProp1,
//			},
//			accessTime: now.Add(3 * time.Hour),
//		},
//	}
//
//	for _, tc := range testCases {
//		providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
//		defer ctrl.Finish()
//
//		expectedOrderedProps := getExpectedOrder(tc.propSubmitOrder, tc.accessTime)
//
//		for _, prop := range tc.propSubmitOrder {
//			cpProp := prop
//			providerKeeper.SetPendingConsumerRemovalProp(ctx, &cpProp)
//		}
//		propsToExecute := providerKeeper.GetConsumerRemovalPropsToExecute(ctx.WithBlockTime(tc.accessTime))
//		require.Equal(t, expectedOrderedProps, propsToExecute)
//	}
//}

// Test getting both matured and pending consumer removal proposals
func TestGetAllConsumerRemovalProps(t *testing.T) {
	pk, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	now := time.Now().UTC()
	props := []providertypes.ConsumerRemovalProposal{
		{ChainId: "chain-2", StopTime: now},
		{ChainId: "chain-1", StopTime: now.Add(2 * time.Hour)},
		{ChainId: "chain-4", StopTime: now.Add(-time.Hour)},
		{ChainId: "chain-3", StopTime: now.Add(4 * time.Hour)},
		{ChainId: "chain-1", StopTime: now},
	}
	expectedGetAllOrder := props
	// sorting by StopTime.UnixNano()
	sort.Slice(expectedGetAllOrder, func(i, j int) bool {
		tsi := uint64(expectedGetAllOrder[i].StopTime.UTC().UnixNano())
		tsj := uint64(expectedGetAllOrder[j].StopTime.UTC().UnixNano())
		cmpTimestamps := bytes.Compare(sdk.Uint64ToBigEndian(tsi), sdk.Uint64ToBigEndian(tsj))
		if cmpTimestamps == 0 {
			// proposals with same StopTime
			return expectedGetAllOrder[i].ChainId < expectedGetAllOrder[j].ChainId
		}
		return cmpTimestamps == -1
	})

	for _, prop := range props {
		cpProp := prop // bring into loop scope - avoids using iterator pointer instead of value pointer
		pk.SetPendingConsumerRemovalProp(ctx, &cpProp)
	}

	// iterate and check all results are returned in the expected order
	result := pk.GetAllPendingConsumerRemovalProps(ctx.WithBlockTime(now))
	require.Len(t, result, len(props))
	require.Equal(t, expectedGetAllOrder, result)
}

// TestMakeConsumerGenesis tests the MakeConsumerGenesis keeper method.
// An expected genesis state is hardcoded in json, unmarshaled, and compared
// against an actual consumer genesis state constructed by a provider keeper.
func TestMakeConsumerGenesis(t *testing.T) {
	keeperParams := testkeeper.NewInMemKeeperParams(t)
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, keeperParams)
	moduleParams := providertypes.Params{
		TemplateClient: &ibctmtypes.ClientState{
			TrustLevel:    ibctmtypes.DefaultTrustLevel,
			MaxClockDrift: 10000000000,
			ProofSpecs: []*_go.ProofSpec{
				{
					LeafSpec: &_go.LeafOp{
						Hash:         _go.HashOp_SHA256,
						PrehashKey:   _go.HashOp_NO_HASH,
						PrehashValue: _go.HashOp_SHA256,
						Length:       _go.LengthOp_VAR_PROTO,
						Prefix:       []byte{0x00},
					},
					InnerSpec: &_go.InnerSpec{
						ChildOrder:      []int32{0, 1},
						ChildSize:       33,
						MinPrefixLength: 4,
						MaxPrefixLength: 12,
						Hash:            _go.HashOp_SHA256,
					},
					MaxDepth: 0,
					MinDepth: 0,
				},
				{
					LeafSpec: &_go.LeafOp{
						Hash:         _go.HashOp_SHA256,
						PrehashKey:   _go.HashOp_NO_HASH,
						PrehashValue: _go.HashOp_SHA256,
						Length:       _go.LengthOp_VAR_PROTO,
						Prefix:       []byte{0x00},
					},
					InnerSpec: &_go.InnerSpec{
						ChildOrder:      []int32{0, 1},
						ChildSize:       32,
						MinPrefixLength: 1,
						MaxPrefixLength: 1,
						Hash:            _go.HashOp_SHA256,
					},
					MaxDepth: 0,
				},
			},
			UpgradePath:                  []string{"upgrade", "upgradedIBCState"},
			AllowUpdateAfterExpiry:       true,
			AllowUpdateAfterMisbehaviour: true,
		},
		// Note these are unused provider parameters for this test, and not actually asserted against
		// They must be populated with reasonable values to satisfy SetParams though.
		TrustingPeriodFraction:      providertypes.DefaultTrustingPeriodFraction,
		CcvTimeoutPeriod:            ccvtypes.DefaultCCVTimeoutPeriod,
		SlashMeterReplenishPeriod:   providertypes.DefaultSlashMeterReplenishPeriod,
		SlashMeterReplenishFraction: providertypes.DefaultSlashMeterReplenishFraction,
		ConsumerRewardDenomRegistrationFee: sdk.Coin{
			Denom:  "stake",
			Amount: math.NewInt(1000000),
		},
		BlocksPerEpoch:                        600,
		NumberOfEpochsToStartReceivingRewards: 24,
	}
	providerKeeper.SetParams(ctx, moduleParams)
	defer ctrl.Finish()

	//
	// Other setup not covered by custom template client state
	//
	ctx = ctx.WithChainID("testchain1") // consumerId is obtained from ctx
	ctx = ctx.WithBlockHeight(5)        // RevisionHeight obtained from ctx
	testkeeper.SetupMocksForLastBondedValidatorsExpectation(mocks.MockStakingKeeper, 0, []stakingtypes.Validator{}, 1)
	gomock.InOrder(testkeeper.GetMocksForMakeConsumerGenesis(ctx, &mocks, 1814400000000000)...)

	// matches params from jsonString
	consumerMetadata := providertypes.ConsumerMetadata{
		Name:        "name",
		Description: "description",
	}

	ccvTimeoutPeriod := time.Duration(2419200000000000)
	transferTimeoutPeriod := time.Duration(3600000000000)
	unbondingPeriod := time.Duration(1728000000000000)
	initializationParameters := providertypes.ConsumerInitializationParameters{
		BlocksPerDistributionTransmission: 1000,
		CcvTimeoutPeriod:                  ccvTimeoutPeriod,
		TransferTimeoutPeriod:             transferTimeoutPeriod,
		ConsumerRedistributionFraction:    "0.75",
		HistoricalEntries:                 10000,
		UnbondingPeriod:                   unbondingPeriod,
	}
	providerKeeper.SetConsumerChainId(ctx, "0", "testchain1")
	providerKeeper.SetConsumerMetadata(ctx, "0", consumerMetadata)
	providerKeeper.SetConsumerInitializationParameters(ctx, "0", initializationParameters)

	actualGenesis, _, err := providerKeeper.MakeConsumerGenesis(ctx, "0")
	require.NoError(t, err)

	// JSON string with tabs, newlines and spaces for readability
	jsonString := `{
		"params": {
			"enabled": true,
			"blocks_per_distribution_transmission": 1000,
			"ccv_timeout_period": 2419200000000000,
			"transfer_timeout_period": 3600000000000,
			"consumer_redistribution_fraction": "0.75",
			"historical_entries": 10000,
			"unbonding_period": 1728000000000000,
			"soft_opt_out_threshold": "0",
			"reward_denoms": [],
			"provider_reward_denoms": [],
			"retry_delay_period": 3600000000000
		},
		"new_chain": true,
		"provider" : {
			"client_state": {
				"chain_id": "testchain1",
				"trust_level": {
					"numerator": 1,
					"denominator": 3
				},
				"trusting_period": 1197504000000000,
				"unbonding_period": 1814400000000000,
				"max_clock_drift": 10000000000,
				"frozen_height": {},
				"latest_height": {
					"revision_height": 5
				},
				"proof_specs": [
					{
						"leaf_spec": {
							"hash": 1,
							"prehash_value": 1,
							"length": 1,
							"prefix": "AA=="
						},
						"inner_spec": {
							"child_order": [0, 1],
							"child_size": 33,
							"min_prefix_length": 4,
							"max_prefix_length": 12,
							"hash": 1
						}
					},
					{
						"leaf_spec": {
							"hash": 1,
							"prehash_value": 1,
							"length": 1,
							"prefix": "AA=="
						},
						"inner_spec": {
							"child_order": [0, 1],
							"child_size": 32,
							"min_prefix_length": 1,
							"max_prefix_length": 1,
							"hash": 1
						}
					}
				],
				"upgrade_path": ["upgrade", "upgradedIBCState"],
				"allow_update_after_expiry": true,
				"allow_update_after_misbehaviour": true
			},
			"consensus_state": {
				"timestamp": "2020-01-02T00:00:10Z",
				"root": {
					"hash": "LpGpeyQVLUo9HpdsgJr12NP2eCICspcULiWa5u9udOA="
				},
				"next_validators_hash": "E30CE736441FB9101FADDAF7E578ABBE6DFDB67207112350A9A904D554E1F5BE"
			},
			"initial_val_set": [
				{
					"pub_key": {
						"type": "tendermint/PubKeyEd25519",
						"value": "dcASx5/LIKZqagJWN0frOlFtcvz91frYmj/zmoZRWro="
					},
					"power": 1
				}
			]
		}
	}`

	var expectedGenesis ccvtypes.ConsumerGenesisState
	err = json.Unmarshal([]byte(jsonString), &expectedGenesis) // ignores tabs, newlines and spaces
	require.NoError(t, err)

	// Zeroing out different fields that are challenging to mock
	actualGenesis.Provider.InitialValSet = []abci.ValidatorUpdate{}
	expectedGenesis.Provider.InitialValSet = []abci.ValidatorUpdate{}
	actualGenesis.Provider.ConsensusState = &ibctmtypes.ConsensusState{}
	expectedGenesis.Provider.ConsensusState = &ibctmtypes.ConsensusState{}

	require.Equal(t, expectedGenesis, actualGenesis, "consumer chain genesis created incorrectly")
}

// TestBeginBlockInit directly tests BeginBlockInit against the spec using helpers defined above.
func TestBeginBlockInit(t *testing.T) {
	now := time.Now().UTC()

	keeperParams := testkeeper.NewInMemKeeperParams(t)
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, keeperParams)
	providerKeeper.SetParams(ctx, providertypes.DefaultParams())
	defer ctrl.Finish()
	ctx = ctx.WithBlockTime(now)

	// initialize registration, initialization, and update records
	consumerMetadata := []providertypes.ConsumerMetadata{
		{
			Name:        "name",
			Description: "spawn time passed",
		},
		{
			Name:        "title",
			Description: "spawn time passed",
		},
		{
			Name:        "title",
			Description: "spawn time not passed",
		},
		{
			Name:        "title",
			Description: "opt-in chain with at least one validator opted in",
		},
		{
			Name:        "title",
			Description: "opt-in chain with no validator opted in",
		},
	}
	chainIds := []string{"chain0", "chain1", "chain2", "chain3", "chain4"}

	initializationParameters := []providertypes.ConsumerInitializationParameters{
		{
			InitialHeight:                     clienttypes.NewHeight(3, 4),
			GenesisHash:                       []byte{},
			BinaryHash:                        []byte{},
			SpawnTime:                         now.Add(-time.Hour * 2).UTC(),
			UnbondingPeriod:                   time.Duration(100000000000),
			CcvTimeoutPeriod:                  time.Duration(100000000000),
			TransferTimeoutPeriod:             time.Duration(100000000000),
			ConsumerRedistributionFraction:    "0.75",
			BlocksPerDistributionTransmission: 10,
			HistoricalEntries:                 10000,
			DistributionTransmissionChannel:   "",
		},
		{
			InitialHeight:                     clienttypes.NewHeight(3, 4),
			GenesisHash:                       []byte{},
			BinaryHash:                        []byte{},
			SpawnTime:                         now.Add(-time.Hour).UTC(),
			UnbondingPeriod:                   time.Duration(100000000000),
			CcvTimeoutPeriod:                  time.Duration(100000000000),
			TransferTimeoutPeriod:             time.Duration(100000000000),
			ConsumerRedistributionFraction:    "0.75",
			BlocksPerDistributionTransmission: 10,
			HistoricalEntries:                 10000,
			DistributionTransmissionChannel:   "",
		},
		{
			InitialHeight:                     clienttypes.NewHeight(3, 4),
			GenesisHash:                       []byte{},
			BinaryHash:                        []byte{},
			SpawnTime:                         now.Add(time.Hour).UTC(),
			UnbondingPeriod:                   time.Duration(100000000000),
			CcvTimeoutPeriod:                  time.Duration(100000000000),
			TransferTimeoutPeriod:             time.Duration(100000000000),
			ConsumerRedistributionFraction:    "0.75",
			BlocksPerDistributionTransmission: 10,
			HistoricalEntries:                 10000,
			DistributionTransmissionChannel:   "",
		},
		{
			InitialHeight:                     clienttypes.NewHeight(3, 4),
			GenesisHash:                       []byte{},
			BinaryHash:                        []byte{},
			SpawnTime:                         now.Add(-time.Hour).UTC(),
			UnbondingPeriod:                   time.Duration(100000000000),
			CcvTimeoutPeriod:                  time.Duration(100000000000),
			TransferTimeoutPeriod:             time.Duration(100000000000),
			ConsumerRedistributionFraction:    "0.75",
			BlocksPerDistributionTransmission: 10,
			HistoricalEntries:                 10000,
			DistributionTransmissionChannel:   "",
		},
		{
			InitialHeight:                     clienttypes.NewHeight(3, 4),
			GenesisHash:                       []byte{},
			BinaryHash:                        []byte{},
			SpawnTime:                         now.Add(-time.Minute).UTC(),
			UnbondingPeriod:                   time.Duration(100000000000),
			CcvTimeoutPeriod:                  time.Duration(100000000000),
			TransferTimeoutPeriod:             time.Duration(100000000000),
			ConsumerRedistributionFraction:    "0.75",
			BlocksPerDistributionTransmission: 10,
			HistoricalEntries:                 10000,
			DistributionTransmissionChannel:   "",
		},
	}
	powerShapingParameters := []providertypes.PowerShapingParameters{
		{
			Top_N:              50,
			ValidatorsPowerCap: 0,
			ValidatorSetCap:    0,
			Allowlist:          []string{},
			Denylist:           []string{},
		},
		{
			Top_N:              50,
			ValidatorsPowerCap: 0,
			ValidatorSetCap:    0,
			Allowlist:          []string{},
			Denylist:           []string{},
		},
		{
			Top_N:              50,
			ValidatorsPowerCap: 0,
			ValidatorSetCap:    0,
			Allowlist:          []string{},
			Denylist:           []string{},
		},
		{
			Top_N:              0,
			ValidatorsPowerCap: 0,
			ValidatorSetCap:    0,
			Allowlist:          []string{},
			Denylist:           []string{},
		},
		{
			Top_N:              0,
			ValidatorsPowerCap: 0,
			ValidatorSetCap:    0,
			Allowlist:          []string{},
			Denylist:           []string{},
		}}

	// Expect client creation for only the first, second, and fifth proposals (spawn time already passed and valid)
	expectedCalls := testkeeper.GetMocksForCreateConsumerClient(ctx, &mocks, "chain0", clienttypes.NewHeight(3, 4))
	expectedCalls = append(expectedCalls, testkeeper.GetMocksForCreateConsumerClient(ctx, &mocks, "chain1", clienttypes.NewHeight(3, 4))...)
	expectedCalls = append(expectedCalls, testkeeper.GetMocksForCreateConsumerClient(ctx, &mocks, "chain3", clienttypes.NewHeight(3, 4))...)

	// The fifth chain would have spawn time passed and hence needs the mocks but the client will not be
	// created because `chain4` is an Opt In chain and has no validator opted in
	expectedCalls = append(expectedCalls, testkeeper.GetMocksForCreateConsumerClient(ctx, &mocks, "chain4", clienttypes.NewHeight(3, 4))...)

	gomock.InOrder(expectedCalls...)

	// set up all the records
	for i, chainId := range chainIds {
		providerKeeper.SetConsumerChainId(ctx, fmt.Sprintf("%d", i), chainId)
	}

	for i, r := range consumerMetadata {
		providerKeeper.SetConsumerMetadata(ctx, fmt.Sprintf("%d", i), r)
	}
	for i, r := range initializationParameters {
		providerKeeper.SetConsumerInitializationParameters(ctx, fmt.Sprintf("%d", i), r)
		// set up the chains in their initialized phase, hence they could launch
		providerKeeper.SetConsumerPhase(ctx, fmt.Sprintf("%d", i), providerkeeper.Initialized)
		providerKeeper.AppendSpawnTimeForConsumerToBeLaunched(ctx, fmt.Sprintf("%d", i), r.SpawnTime)
	}
	for i, r := range powerShapingParameters {
		providerKeeper.SetConsumerPowerShapingParameters(ctx, fmt.Sprintf("%d", i), r)
	}

	// opt in a sample validator so the chain's proposal can successfully execute
	validator := cryptotestutil.NewCryptoIdentityFromIntSeed(0).SDKStakingValidator()
	consAddr, _ := validator.GetConsAddr()
	testkeeper.SetupMocksForLastBondedValidatorsExpectation(mocks.MockStakingKeeper, 1, []stakingtypes.Validator{validator}, -1) // -1 to allow any number of calls

	valAddr, _ := sdk.ValAddressFromBech32(validator.GetOperator())
	mocks.MockStakingKeeper.EXPECT().GetLastValidatorPower(gomock.Any(), valAddr).Return(int64(1), nil).AnyTimes()
	// for the validator, expect a call to GetValidatorByConsAddr with its consensus address
	mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(gomock.Any(), consAddr).Return(validator, nil).AnyTimes()

	providerKeeper.SetOptedIn(ctx, "3", providertypes.NewProviderConsAddress(consAddr))

	providerKeeper.BeginBlockInit(ctx)

	// first chain was successfully launched
	phase, found := providerKeeper.GetConsumerPhase(ctx, "0")
	require.True(t, found)
	require.Equal(t, providerkeeper.Launched, phase)
	_, found = providerKeeper.GetConsumerGenesis(ctx, "0")
	require.True(t, found)

	// second chain was successfully launched
	phase, found = providerKeeper.GetConsumerPhase(ctx, "1")
	require.True(t, found)
	require.Equal(t, providerkeeper.Launched, phase)
	_, found = providerKeeper.GetConsumerGenesis(ctx, "1")
	require.True(t, found)

	// third chain was not launched because its spawn time has not passed
	phase, found = providerKeeper.GetConsumerPhase(ctx, "2")
	require.True(t, found)
	require.Equal(t, providerkeeper.Initialized, phase)
	_, found = providerKeeper.GetConsumerGenesis(ctx, "2")
	require.False(t, found)

	// fourth chain corresponds to an Opt-In chain with one opted-in validator and hence the chain gets
	// successfully executed
	phase, found = providerKeeper.GetConsumerPhase(ctx, "3")
	require.True(t, found)
	require.Equal(t, providerkeeper.Launched, phase)
	_, found = providerKeeper.GetConsumerGenesis(ctx, "3")
	require.True(t, found)

	// fifth chain corresponds to an Opt-In chain with no opted-in validators and hence the
	// chain launch is NOT successful
	phase, found = providerKeeper.GetConsumerPhase(ctx, "4")
	require.True(t, found)
	require.Equal(t, providerkeeper.Initialized, phase)
	_, found = providerKeeper.GetConsumerGenesis(ctx, "4")
	require.False(t, found)
}

func TestBeginBlockCCR(t *testing.T) {
	now := time.Now().UTC()

	keeperParams := testkeeper.NewInMemKeeperParams(t)
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, keeperParams)
	providerKeeper.SetParams(ctx, providertypes.DefaultParams())
	defer ctrl.Finish()
	ctx = ctx.WithBlockTime(now)

	chainIds := []string{"chain1", "chain2", "chain3"}
	consumerIds := []string{"consumerId1", "consumerId2", "consumerId3"}
	providerKeeper.SetConsumerStopTime(ctx, consumerIds[0], now.Add(-time.Hour))
	providerKeeper.AppendStopTimeForConsumerToBeStopped(ctx, consumerIds[0], now.Add(-time.Hour))
	providerKeeper.SetConsumerStopTime(ctx, consumerIds[1], now)
	providerKeeper.AppendStopTimeForConsumerToBeStopped(ctx, consumerIds[1], now)
	providerKeeper.SetConsumerStopTime(ctx, consumerIds[2], now.Add(time.Hour))
	providerKeeper.AppendStopTimeForConsumerToBeStopped(ctx, consumerIds[2], now.Add(time.Hour))

	//
	// Mock expectations
	//
	expectations := []*gomock.Call{}
	for i, _ := range consumerIds {
		chainId := chainIds[i]
		// A consumer chain is setup corresponding to each consumerId, making these mocks necessary
		testkeeper.SetupMocksForLastBondedValidatorsExpectation(mocks.MockStakingKeeper, 0, []stakingtypes.Validator{}, 1)
		expectations = append(expectations, testkeeper.GetMocksForCreateConsumerClient(ctx, &mocks,
			chainId, clienttypes.NewHeight(2, 3))...)
		expectations = append(expectations, testkeeper.GetMocksForSetConsumerChain(ctx, &mocks, chainId)...)
	}
	// Only first two consumer chains should be stopped
	expectations = append(expectations, testkeeper.GetMocksForStopConsumerChainWithCloseChannel(ctx, &mocks)...)
	expectations = append(expectations, testkeeper.GetMocksForStopConsumerChainWithCloseChannel(ctx, &mocks)...)

	gomock.InOrder(expectations...)

	//
	// Remaining setup
	//
	for i, consumerId := range consumerIds {
		// Setup a valid consumer chain for each consumerId
		initializationRecord := testkeeper.GetTestInitializationParameters()
		initializationRecord.InitialHeight = clienttypes.NewHeight(2, 3)
		registrationRecord := testkeeper.GetTestConsumerMetadata()

		providerKeeper.SetConsumerChainId(ctx, consumerId, chainIds[i])
		providerKeeper.SetConsumerMetadata(ctx, consumerId, registrationRecord)
		providerKeeper.SetConsumerInitializationParameters(ctx, consumerId, initializationRecord)
		providerKeeper.SetConsumerPowerShapingParameters(ctx, consumerId, testkeeper.GetTestPowerShapingParameters())
		providerKeeper.SetConsumerPhase(ctx, consumerId, providerkeeper.Initialized)
		providerKeeper.SetClientIdToConsumerId(ctx, "clientID", consumerId)

		err := providerKeeper.CreateConsumerClient(ctx, consumerId)
		require.NoError(t, err)
		err = providerKeeper.SetConsumerChain(ctx, "channelID")
		require.NoError(t, err)

		// after we have created the consumer client, the chain is considered launched and hence we could later stop the chain
		providerKeeper.SetConsumerPhase(ctx, consumerId, providerkeeper.Launched)
	}

	//
	// Test execution
	//

	providerKeeper.BeginBlockCCR(ctx)

	// Only the 3rd (final) proposal is still stored as pending
	phase, found := providerKeeper.GetConsumerPhase(ctx, consumerIds[0])
	require.True(t, found)
	require.Equal(t, providerkeeper.Stopped, phase)
	phase, found = providerKeeper.GetConsumerPhase(ctx, consumerIds[1])
	require.True(t, found)
	require.Equal(t, providerkeeper.Stopped, phase)
	// third chain had a stopTime in the future and hence did not stop
	phase, found = providerKeeper.GetConsumerPhase(ctx, consumerIds[2])
	require.True(t, found)
	require.Equal(t, providerkeeper.Launched, phase)
}
