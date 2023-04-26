package keeper_test

import (
	"bytes"
	"encoding/json"
	"sort"
	"testing"
	"time"

	_go "github.com/confio/ics23/go"
	sdk "github.com/cosmos/cosmos-sdk/types"
	evidencetypes "github.com/cosmos/cosmos-sdk/x/evidence/types"
	clienttypes "github.com/cosmos/ibc-go/v4/modules/core/02-client/types"
	ibctmtypes "github.com/cosmos/ibc-go/v4/modules/light-clients/07-tendermint/types"
	"github.com/golang/mock/gomock"
	abci "github.com/tendermint/tendermint/abci/types"

	"github.com/stretchr/testify/require"

	cryptoutil "github.com/cosmos/interchain-security/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	providerkeeper "github.com/cosmos/interchain-security/x/ccv/provider/keeper"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"
)

//
// Initialization sub-protocol related tests of proposal.go
//

// Tests the HandleConsumerAdditionProposal method against the SpawnConsumerChainProposalHandler spec.
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-hcaprop1
// Spec tag: [CCV-PCF-HCAPROP.1]
func TestHandleConsumerAdditionProposal(t *testing.T) {
	type testCase struct {
		description string
		malleate    func(ctx sdk.Context, k providerkeeper.Keeper, chainID string)
		prop        *ccvtypes.ConsumerAdditionProposal
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
			prop: ccvtypes.NewConsumerAdditionProposal(
				"title",
				"description",
				"chainID",
				clienttypes.NewHeight(2, 3),
				[]byte("gen_hash"),
				[]byte("bin_hash"),
				now, // Spawn time
				"0.75",
				10,
				10000,
				100000000000,
				100000000000,
				100000000000,
			).(*ccvtypes.ConsumerAdditionProposal),
			blockTime:     now,
			expAppendProp: true,
		},
		{
			description: "expect to not append invalid proposal using an already existing chain id",
			malleate: func(ctx sdk.Context, k providerkeeper.Keeper, chainID string) {
				k.SetConsumerClientId(ctx, chainID, "anyClientId")
			},

			prop: ccvtypes.NewConsumerAdditionProposal(
				"title",
				"description",
				"chainID",
				clienttypes.NewHeight(2, 3),
				[]byte("gen_hash"),
				[]byte("bin_hash"),
				now,
				"0.75",
				10,
				10000,
				100000000000,
				100000000000,
				100000000000,
			).(*ccvtypes.ConsumerAdditionProposal),
			blockTime:     now,
			expAppendProp: false,
		},
	}

	for _, tc := range tests {
		// Common setup
		keeperParams := testkeeper.NewInMemKeeperParams(t)
		providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, keeperParams)
		providerKeeper.SetParams(ctx, ccvtypes.DefaultProviderParams())
		ctx = ctx.WithBlockTime(tc.blockTime)

		if tc.expAppendProp {
			// Mock calls are only asserted if we expect a client to be created.
			gomock.InOrder(
				testkeeper.GetMocksForCreateConsumerClient(ctx, &mocks, tc.prop.ChainId, clienttypes.NewHeight(2, 3))...,
			)
		}

		tc.malleate(ctx, providerKeeper, tc.prop.ChainId)

		err := providerKeeper.HandleConsumerAdditionProposal(ctx, tc.prop)

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

// Tests the CreateConsumerClient method against the spec,
// with more granularity than what's covered in TestHandleCreateConsumerChainProposal.
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-crclient1
// Spec tag: [CCV-PCF-CRCLIENT.1]
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
				// Valid client creation is asserted with mock expectations here
				gomock.InOrder(
					testkeeper.GetMocksForCreateConsumerClient(ctx, mocks, "chainID", clienttypes.NewHeight(4, 5))...,
				)
			},
			expClientCreated: true,
		},
		{
			description: "client for this chain already exists, new one is not created",
			setup: func(providerKeeper *providerkeeper.Keeper, ctx sdk.Context, mocks *testkeeper.MockedKeepers) {
				providerKeeper.SetConsumerClientId(ctx, "chainID", "clientID")

				// Expect none of the client creation related calls to happen
				mocks.MockStakingKeeper.EXPECT().UnbondingTime(gomock.Any()).Times(0)
				mocks.MockClientKeeper.EXPECT().CreateClient(gomock.Any(), gomock.Any(), gomock.Any()).Times(0)
				mocks.MockClientKeeper.EXPECT().GetSelfConsensusState(gomock.Any(), gomock.Any()).Times(0)
				mocks.MockStakingKeeper.EXPECT().IterateLastValidatorPowers(gomock.Any(), gomock.Any()).Times(0)
			},
			expClientCreated: false,
		},
	}

	for _, tc := range tests {
		// Common setup
		keeperParams := testkeeper.NewInMemKeeperParams(t)
		providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, keeperParams)
		providerKeeper.SetParams(ctx, ccvtypes.DefaultProviderParams())

		// Test specific setup
		tc.setup(&providerKeeper, ctx, &mocks)

		// Call method with same arbitrary values as defined above in mock expectations.
		err := providerKeeper.CreateConsumerClient(ctx, testkeeper.GetTestConsumerAdditionProp())

		if tc.expClientCreated {
			require.NoError(t, err)
			testCreatedConsumerClient(t, ctx, providerKeeper, "chainID", "clientID")
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
	ctx sdk.Context, providerKeeper providerkeeper.Keeper, expectedChainID string, expectedClientID string,
) {
	t.Helper()
	// ClientID should be stored.
	clientId, found := providerKeeper.GetConsumerClientId(ctx, expectedChainID)
	require.True(t, found, "consumer client not found")
	require.Equal(t, expectedClientID, clientId)

	// Only assert that consumer genesis was set,
	// more granular tests on consumer genesis should be defined in TestMakeConsumerGenesis
	_, ok := providerKeeper.GetConsumerGenesis(ctx, expectedChainID)
	require.True(t, ok)
}

// TestPendingConsumerAdditionPropDeletion tests the getting/setting
// and deletion keeper methods for pending consumer addition props
func TestPendingConsumerAdditionPropDeletion(t *testing.T) {
	testCases := []struct {
		ccvtypes.ConsumerAdditionProposal
		ExpDeleted bool
	}{
		{
			ConsumerAdditionProposal: ccvtypes.ConsumerAdditionProposal{ChainId: "0", SpawnTime: time.Now().UTC()},
			ExpDeleted:               true,
		},
		{
			ConsumerAdditionProposal: ccvtypes.ConsumerAdditionProposal{ChainId: "1", SpawnTime: time.Now().UTC().Add(time.Hour)},
			ExpDeleted:               false,
		},
	}
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	for _, tc := range testCases {
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
	sampleProp1 := ccvtypes.ConsumerAdditionProposal{ChainId: "chain-2", SpawnTime: now}
	sampleProp2 := ccvtypes.ConsumerAdditionProposal{ChainId: "chain-1", SpawnTime: now.Add(time.Hour)}
	sampleProp3 := ccvtypes.ConsumerAdditionProposal{ChainId: "chain-4", SpawnTime: now.Add(-time.Hour)}
	sampleProp4 := ccvtypes.ConsumerAdditionProposal{ChainId: "chain-3", SpawnTime: now}
	sampleProp5 := ccvtypes.ConsumerAdditionProposal{ChainId: "chain-1", SpawnTime: now.Add(2 * time.Hour)}

	getExpectedOrder := func(props []ccvtypes.ConsumerAdditionProposal, accessTime time.Time) []ccvtypes.ConsumerAdditionProposal {
		expectedOrder := []ccvtypes.ConsumerAdditionProposal{}
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
		propSubmitOrder []ccvtypes.ConsumerAdditionProposal
		accessTime      time.Time
	}{
		{
			propSubmitOrder: []ccvtypes.ConsumerAdditionProposal{
				sampleProp1, sampleProp2, sampleProp3, sampleProp4, sampleProp5,
			},
			accessTime: now,
		},
		{
			propSubmitOrder: []ccvtypes.ConsumerAdditionProposal{
				sampleProp3, sampleProp2, sampleProp1, sampleProp5, sampleProp4,
			},
			accessTime: now.Add(time.Hour),
		},
		{
			propSubmitOrder: []ccvtypes.ConsumerAdditionProposal{
				sampleProp5, sampleProp4, sampleProp3, sampleProp2, sampleProp1,
			},
			accessTime: now.Add(-2 * time.Hour),
		},
		{
			propSubmitOrder: []ccvtypes.ConsumerAdditionProposal{
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
	props := []ccvtypes.ConsumerAdditionProposal{
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

//
// Consumer Chain Removal sub-protocol related tests of proposal.go
//

// TestHandleConsumerRemovalProposal tests HandleConsumerRemovalProposal against its corresponding spec method.
//
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-hcrprop1
// Spec tag: [CCV-PCF-HCRPROP.1]
func TestHandleConsumerRemovalProposal(t *testing.T) {
	type testCase struct {
		description string
		setupMocks  func(ctx sdk.Context, k providerkeeper.Keeper, chainID string)

		// Consumer removal proposal to handle
		prop *ccvtypes.ConsumerRemovalProposal
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
			prop: ccvtypes.NewConsumerRemovalProposal(
				"title",
				"description",
				"chainID",
				now,
			).(*ccvtypes.ConsumerRemovalProposal),
			blockTime:     hourAfterNow, // After stop time.
			expAppendProp: true,
			chainId:       "chainID",
		},
		{
			description: "valid proposal - stop_time in the past",
			setupMocks: func(ctx sdk.Context, k providerkeeper.Keeper, chainID string) {
				k.SetConsumerClientId(ctx, chainID, "ClientID")
			},
			prop: ccvtypes.NewConsumerRemovalProposal(
				"title",
				"description",
				"chainID",
				hourBeforeNow,
			).(*ccvtypes.ConsumerRemovalProposal),
			blockTime:     hourAfterNow, // After stop time.
			expAppendProp: true,
			chainId:       "chainID",
		},
		{
			description: "valid proposal - before stop_time in the future",
			setupMocks: func(ctx sdk.Context, k providerkeeper.Keeper, chainID string) {
				k.SetConsumerClientId(ctx, chainID, "ClientID")
			},
			prop: ccvtypes.NewConsumerRemovalProposal(
				"title",
				"description",
				"chainID",
				hourAfterNow,
			).(*ccvtypes.ConsumerRemovalProposal),
			blockTime:     now,
			expAppendProp: true,
			chainId:       "chainID",
		},
		{
			description: "rejected valid proposal - consumer chain does not exist",
			setupMocks:  func(ctx sdk.Context, k providerkeeper.Keeper, chainID string) {},
			prop: ccvtypes.NewConsumerRemovalProposal(
				"title",
				"description",
				"chainID-2",
				hourAfterNow,
			).(*ccvtypes.ConsumerRemovalProposal),
			blockTime:     hourAfterNow, // After stop time.
			expAppendProp: false,
			chainId:       "chainID-2",
		},
	}

	for _, tc := range tests {

		// Common setup
		keeperParams := testkeeper.NewInMemKeeperParams(t)
		providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, keeperParams)
		providerKeeper.SetParams(ctx, ccvtypes.DefaultProviderParams())
		ctx = ctx.WithBlockTime(tc.blockTime)

		// Mock expectations and setup for stopping the consumer chain, if applicable
		// Note: when expAppendProp is false, no mocks are setup,
		// meaning no external keeper methods are allowed to be called.
		if tc.expAppendProp {
			testkeeper.SetupForStoppingConsumerChain(t, ctx, &providerKeeper, mocks)
		}

		tc.setupMocks(ctx, providerKeeper, tc.prop.ChainId)

		err := providerKeeper.HandleConsumerRemovalProposal(ctx, tc.prop)

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

// Tests the StopConsumerChain method against the spec,
// with more granularity than what's covered in TestHandleConsumerRemovalProposal, or integration tests.
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

	tests := []testCase{
		{
			description: "proposal dropped, client doesn't exist",
			setup: func(ctx sdk.Context, providerKeeper *providerkeeper.Keeper, mocks testkeeper.MockedKeepers) {
				// No mocks, meaning no external keeper methods are allowed to be called.
			},
			expErr: true,
		},
		{
			description: "valid stop of consumer chain, throttle related queues are cleaned",
			setup: func(ctx sdk.Context, providerKeeper *providerkeeper.Keeper, mocks testkeeper.MockedKeepers) {
				testkeeper.SetupForStoppingConsumerChain(t, ctx, providerKeeper, mocks)

				providerKeeper.QueueGlobalSlashEntry(ctx, ccvtypes.NewGlobalSlashEntry(
					ctx.BlockTime(), "chainID", 1, cryptoutil.NewCryptoIdentityFromIntSeed(90).ProviderConsAddress()))

				err := providerKeeper.QueueThrottledSlashPacketData(ctx, "chainID", 1, testkeeper.GetNewSlashPacketData())
				if err != nil {
					t.Fatal(err)
				}
				err = providerKeeper.QueueThrottledVSCMaturedPacketData(ctx, "chainID", 2, testkeeper.GetNewVSCMaturedPacketData())
				if err != nil {
					t.Fatal(err)
				}
			},
			expErr: false,
		},
		{
			description: "valid stop of consumer chain, all mock calls hit",
			setup: func(ctx sdk.Context, providerKeeper *providerkeeper.Keeper, mocks testkeeper.MockedKeepers) {
				testkeeper.SetupForStoppingConsumerChain(t, ctx, providerKeeper, mocks)
			},
			expErr: false,
		},
	}

	for _, tc := range tests {

		// Common setup
		keeperParams := testkeeper.NewInMemKeeperParams(t)
		providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, keeperParams)
		providerKeeper.SetParams(ctx, ccvtypes.DefaultProviderParams())

		// Setup specific to test case
		tc.setup(ctx, &providerKeeper, mocks)

		err := providerKeeper.StopConsumerChain(ctx, "chainID", true)

		if tc.expErr {
			require.Error(t, err)
		} else {
			require.NoError(t, err)
		}

		testProviderStateIsCleaned(t, ctx, providerKeeper, "chainID", "channelID")

		ctrl.Finish()
	}
}

// testProviderStateIsCleaned executes test assertions for the proposer's state being cleaned after a stopped consumer chain.
func testProviderStateIsCleaned(t *testing.T, ctx sdk.Context, providerKeeper providerkeeper.Keeper,
	expectedChainID string, expectedChannelID string,
) {
	t.Helper()
	_, found := providerKeeper.GetConsumerClientId(ctx, expectedChainID)
	require.False(t, found)
	_, found = providerKeeper.GetChainToChannel(ctx, expectedChainID)
	require.False(t, found)
	_, found = providerKeeper.GetChannelToChain(ctx, expectedChannelID)
	require.False(t, found)
	_, found = providerKeeper.GetInitChainHeight(ctx, expectedChainID)
	require.False(t, found)
	acks := providerKeeper.GetSlashAcks(ctx, expectedChainID)
	require.Empty(t, acks)
	_, found = providerKeeper.GetInitTimeoutTimestamp(ctx, expectedChainID)
	require.False(t, found)

	require.Empty(t, providerKeeper.GetAllVscSendTimestamps(ctx, expectedChainID))

	// test key assignment state is cleaned
	require.Empty(t, providerKeeper.GetAllValidatorConsumerPubKeys(ctx, &expectedChainID))
	require.Empty(t, providerKeeper.GetAllValidatorsByConsumerAddr(ctx, &expectedChainID))
	require.Empty(t, providerKeeper.GetAllKeyAssignmentReplacements(ctx, expectedChainID))
	require.Empty(t, providerKeeper.GetAllConsumerAddrsToPrune(ctx, expectedChainID))

	allGlobalEntries := providerKeeper.GetAllGlobalSlashEntries(ctx)
	for _, entry := range allGlobalEntries {
		require.NotEqual(t, expectedChainID, entry.ConsumerChainID)
	}

	slashPacketData, vscMaturedPacketData, _, _ := providerKeeper.GetAllThrottledPacketData(ctx, expectedChainID)
	require.Empty(t, slashPacketData)
	require.Empty(t, vscMaturedPacketData)
}

// TestPendingConsumerRemovalPropDeletion tests the getting/setting
// and deletion methods for pending consumer removal props
func TestPendingConsumerRemovalPropDeletion(t *testing.T) {
	testCases := []struct {
		ccvtypes.ConsumerRemovalProposal
		ExpDeleted bool
	}{
		{
			ConsumerRemovalProposal: ccvtypes.ConsumerRemovalProposal{ChainId: "8", StopTime: time.Now().UTC()},
			ExpDeleted:              true,
		},
		{
			ConsumerRemovalProposal: ccvtypes.ConsumerRemovalProposal{ChainId: "9", StopTime: time.Now().UTC().Add(time.Hour)},
			ExpDeleted:              false,
		},
	}
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	for _, tc := range testCases {
		providerKeeper.SetPendingConsumerRemovalProp(ctx, &tc.ConsumerRemovalProposal)
	}

	ctx = ctx.WithBlockTime(time.Now().UTC())

	propsToExecute := providerKeeper.GetConsumerRemovalPropsToExecute(ctx)
	// Delete consumer removal proposals, same as what would be done by BeginBlockCCR
	providerKeeper.DeletePendingConsumerRemovalProps(ctx, propsToExecute...)
	numDeleted := 0
	for _, tc := range testCases {
		res := providerKeeper.PendingConsumerRemovalPropExists(ctx, tc.ChainId, tc.StopTime)
		if !tc.ExpDeleted {
			require.NotEmpty(t, res, "consumer removal prop was deleted: %s %s", tc.ChainId, tc.StopTime.String())
			continue
		}
		require.Empty(t, res, "consumer removal prop was not deleted %s %s", tc.ChainId, tc.StopTime.String())
		require.Equal(t, propsToExecute[numDeleted].ChainId, tc.ChainId)
		numDeleted += 1
	}
}

// TestGetConsumerRemovalPropsToExecute tests that pending consumer removal proposals
// that are ready to execute are accessed in order by timestamp via the iterator
func TestGetConsumerRemovalPropsToExecute(t *testing.T) {
	now := time.Now().UTC()
	sampleProp1 := ccvtypes.ConsumerRemovalProposal{ChainId: "chain-2", StopTime: now}
	sampleProp2 := ccvtypes.ConsumerRemovalProposal{ChainId: "chain-1", StopTime: now.Add(time.Hour)}
	sampleProp3 := ccvtypes.ConsumerRemovalProposal{ChainId: "chain-4", StopTime: now.Add(-time.Hour)}
	sampleProp4 := ccvtypes.ConsumerRemovalProposal{ChainId: "chain-3", StopTime: now}
	sampleProp5 := ccvtypes.ConsumerRemovalProposal{ChainId: "chain-1", StopTime: now.Add(2 * time.Hour)}

	getExpectedOrder := func(props []ccvtypes.ConsumerRemovalProposal, accessTime time.Time) []ccvtypes.ConsumerRemovalProposal {
		expectedOrder := []ccvtypes.ConsumerRemovalProposal{}
		for _, prop := range props {
			if !accessTime.Before(prop.StopTime) {
				expectedOrder = append(expectedOrder, prop)
			}
		}
		// sorting by SpawnTime.UnixNano()
		sort.Slice(expectedOrder, func(i, j int) bool {
			if expectedOrder[i].StopTime.UTC() == expectedOrder[j].StopTime.UTC() {
				// proposals with same StopTime
				return expectedOrder[i].ChainId < expectedOrder[j].ChainId
			}
			return expectedOrder[i].StopTime.UTC().Before(expectedOrder[j].StopTime.UTC())
		})
		return expectedOrder
	}

	testCases := []struct {
		propSubmitOrder []ccvtypes.ConsumerRemovalProposal
		accessTime      time.Time
	}{
		{
			propSubmitOrder: []ccvtypes.ConsumerRemovalProposal{
				sampleProp1, sampleProp2, sampleProp3, sampleProp4, sampleProp5,
			},
			accessTime: now,
		},
		{
			propSubmitOrder: []ccvtypes.ConsumerRemovalProposal{
				sampleProp3, sampleProp2, sampleProp1, sampleProp5, sampleProp4,
			},
			accessTime: now.Add(time.Hour),
		},
		{
			propSubmitOrder: []ccvtypes.ConsumerRemovalProposal{
				sampleProp5, sampleProp4, sampleProp3, sampleProp2, sampleProp1,
			},
			accessTime: now.Add(-2 * time.Hour),
		},
		{
			propSubmitOrder: []ccvtypes.ConsumerRemovalProposal{
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
			providerKeeper.SetPendingConsumerRemovalProp(ctx, &cpProp)
		}
		propsToExecute := providerKeeper.GetConsumerRemovalPropsToExecute(ctx.WithBlockTime(tc.accessTime))
		require.Equal(t, expectedOrderedProps, propsToExecute)
	}
}

// Test getting both matured and pending consumer removal proposals
func TestGetAllConsumerRemovalProps(t *testing.T) {
	pk, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	now := time.Now().UTC()
	props := []ccvtypes.ConsumerRemovalProposal{
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
	moduleParams := ccvtypes.ProviderParams{
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
		TrustingPeriodFraction:      ccvtypes.DefaultTrustingPeriodFraction,
		CcvTimeoutPeriod:            ccvtypes.DefaultCCVTimeoutPeriod,
		InitTimeoutPeriod:           ccvtypes.DefaultInitTimeoutPeriod,
		VscTimeoutPeriod:            ccvtypes.DefaultVscTimeoutPeriod,
		SlashMeterReplenishPeriod:   ccvtypes.DefaultSlashMeterReplenishPeriod,
		SlashMeterReplenishFraction: ccvtypes.DefaultSlashMeterReplenishFraction,
		MaxThrottledPackets:         ccvtypes.DefaultMaxThrottledPackets,
	}
	providerKeeper.SetParams(ctx, moduleParams)
	defer ctrl.Finish()

	//
	// Other setup not covered by custom template client state
	//
	ctx = ctx.WithChainID("testchain1") // chainID is obtained from ctx
	ctx = ctx.WithBlockHeight(5)        // RevisionHeight obtained from ctx
	gomock.InOrder(testkeeper.GetMocksForMakeConsumerGenesis(ctx, &mocks, 1814400000000000)...)

	// matches params from jsonString
	prop := ccvtypes.ConsumerAdditionProposal{
		Title:                             "title",
		Description:                       "desc",
		ChainId:                           "testchain1",
		BlocksPerDistributionTransmission: 1000,
		CcvTimeoutPeriod:                  2419200000000000,
		TransferTimeoutPeriod:             3600000000000,
		ConsumerRedistributionFraction:    "0.75",
		HistoricalEntries:                 10000,
		UnbondingPeriod:                   1728000000000000,
	}
	actualGenesis, _, err := providerKeeper.MakeConsumerGenesis(ctx, &prop)
	require.NoError(t, err)

	jsonString := `{"params":{"enabled":true, "blocks_per_distribution_transmission":1000, "ccv_timeout_period":2419200000000000, "transfer_timeout_period": 3600000000000, "consumer_redistribution_fraction":"0.75", "historical_entries":10000, "unbonding_period": 1728000000000000, "soft_opt_out_threshold": "0.05"},"new_chain":true,"provider_client_state":{"chain_id":"testchain1","trust_level":{"numerator":1,"denominator":3},"trusting_period":1197504000000000,"unbonding_period":1814400000000000,"max_clock_drift":10000000000,"frozen_height":{},"latest_height":{"revision_height":5},"proof_specs":[{"leaf_spec":{"hash":1,"prehash_value":1,"length":1,"prefix":"AA=="},"inner_spec":{"child_order":[0,1],"child_size":33,"min_prefix_length":4,"max_prefix_length":12,"hash":1}},{"leaf_spec":{"hash":1,"prehash_value":1,"length":1,"prefix":"AA=="},"inner_spec":{"child_order":[0,1],"child_size":32,"min_prefix_length":1,"max_prefix_length":1,"hash":1}}],"upgrade_path":["upgrade","upgradedIBCState"],"allow_update_after_expiry":true,"allow_update_after_misbehaviour":true},"provider_consensus_state":{"timestamp":"2020-01-02T00:00:10Z","root":{"hash":"LpGpeyQVLUo9HpdsgJr12NP2eCICspcULiWa5u9udOA="},"next_validators_hash":"E30CE736441FB9101FADDAF7E578ABBE6DFDB67207112350A9A904D554E1F5BE"},"unbonding_sequences":null,"initial_val_set":[{"pub_key":{"type":"tendermint/PubKeyEd25519","value":"dcASx5/LIKZqagJWN0frOlFtcvz91frYmj/zmoZRWro="},"power":1}]}`

	var expectedGenesis ccvtypes.ConsumerGenesisState
	err = json.Unmarshal([]byte(jsonString), &expectedGenesis)
	require.NoError(t, err)

	// Zeroing out different fields that are challenging to mock
	actualGenesis.InitialValSet = []abci.ValidatorUpdate{}
	expectedGenesis.InitialValSet = []abci.ValidatorUpdate{}
	actualGenesis.ProviderConsensusState = &ibctmtypes.ConsensusState{}
	expectedGenesis.ProviderConsensusState = &ibctmtypes.ConsensusState{}

	require.Equal(t, expectedGenesis, actualGenesis, "consumer chain genesis created incorrectly")
}

// TestBeginBlockInit directly tests BeginBlockInit against the spec using helpers defined above.
//
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-bblock-init1
// Spec tag:[CCV-PCF-BBLOCK-INIT.1]
func TestBeginBlockInit(t *testing.T) {
	now := time.Now().UTC()

	keeperParams := testkeeper.NewInMemKeeperParams(t)
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, keeperParams)
	providerKeeper.SetParams(ctx, ccvtypes.DefaultProviderParams())
	defer ctrl.Finish()
	ctx = ctx.WithBlockTime(now)

	pendingProps := []*ccvtypes.ConsumerAdditionProposal{
		ccvtypes.NewConsumerAdditionProposal(
			"title", "spawn time passed", "chain1", clienttypes.NewHeight(3, 4), []byte{}, []byte{},
			now.Add(-time.Hour*2).UTC(),
			"0.75",
			10,
			10000,
			100000000000,
			100000000000,
			100000000000,
		).(*ccvtypes.ConsumerAdditionProposal),
		ccvtypes.NewConsumerAdditionProposal(
			"title", "spawn time passed", "chain2", clienttypes.NewHeight(3, 4), []byte{}, []byte{},
			now.Add(-time.Hour*1).UTC(),
			"0.75",
			10,
			10000,
			100000000000,
			100000000000,
			100000000000,
		).(*ccvtypes.ConsumerAdditionProposal),
		ccvtypes.NewConsumerAdditionProposal(
			"title", "spawn time not passed", "chain3", clienttypes.NewHeight(3, 4), []byte{}, []byte{},
			now.Add(time.Hour).UTC(),
			"0.75",
			10,
			10000,
			100000000000,
			100000000000,
			100000000000,
		).(*ccvtypes.ConsumerAdditionProposal),
		ccvtypes.NewConsumerAdditionProposal(
			"title", "invalid proposal: chain id already exists", "chain2", clienttypes.NewHeight(4, 5), []byte{}, []byte{},
			now.UTC(),
			"0.75",
			10,
			10000,
			100000000000,
			100000000000,
			100000000000,
		).(*ccvtypes.ConsumerAdditionProposal),
	}

	// Expect client creation for only for the 1st and second proposals (spawn time already passed and valid)
	gomock.InOrder(
		append(testkeeper.GetMocksForCreateConsumerClient(ctx, &mocks, "chain1", clienttypes.NewHeight(3, 4)),
			testkeeper.GetMocksForCreateConsumerClient(ctx, &mocks, "chain2", clienttypes.NewHeight(3, 4))...)...,
	)

	for _, prop := range pendingProps {
		providerKeeper.SetPendingConsumerAdditionProp(ctx, prop)
	}

	providerKeeper.BeginBlockInit(ctx)

	// Only the third proposal is still stored as pending
	_, found := providerKeeper.GetPendingConsumerAdditionProp(
		ctx, pendingProps[0].SpawnTime, pendingProps[0].ChainId)
	require.False(t, found)

	_, found = providerKeeper.GetPendingConsumerAdditionProp(
		ctx, pendingProps[1].SpawnTime, pendingProps[1].ChainId)
	require.False(t, found)

	_, found = providerKeeper.GetPendingConsumerAdditionProp(
		ctx, pendingProps[2].SpawnTime, pendingProps[2].ChainId)
	require.True(t, found)

	// check that the invalid proposal was dropped
	_, found = providerKeeper.GetPendingConsumerAdditionProp(
		ctx, pendingProps[3].SpawnTime, pendingProps[3].ChainId)
	require.False(t, found)
}

// TestBeginBlockCCR tests BeginBlockCCR against the spec.
//
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-bblock-ccr1
// Spec tag: [CCV-PCF-BBLOCK-CCR.1]
func TestBeginBlockCCR(t *testing.T) {
	now := time.Now().UTC()

	keeperParams := testkeeper.NewInMemKeeperParams(t)
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, keeperParams)
	providerKeeper.SetParams(ctx, ccvtypes.DefaultProviderParams())
	defer ctrl.Finish()
	ctx = ctx.WithBlockTime(now)

	pendingProps := []*ccvtypes.ConsumerRemovalProposal{
		ccvtypes.NewConsumerRemovalProposal(
			"title", "description", "chain1", now.Add(-time.Hour).UTC(),
		).(*ccvtypes.ConsumerRemovalProposal),
		ccvtypes.NewConsumerRemovalProposal(
			"title", "description", "chain2", now,
		).(*ccvtypes.ConsumerRemovalProposal),
		ccvtypes.NewConsumerRemovalProposal(
			"title", "description", "chain3", now.Add(time.Hour).UTC(),
		).(*ccvtypes.ConsumerRemovalProposal),
	}

	//
	// Mock expectations
	//
	expectations := []*gomock.Call{}
	for _, prop := range pendingProps {
		// A consumer chain is setup corresponding to each prop, making these mocks necessary
		expectations = append(expectations, testkeeper.GetMocksForCreateConsumerClient(ctx, &mocks,
			prop.ChainId, clienttypes.NewHeight(2, 3))...)
		expectations = append(expectations, testkeeper.GetMocksForSetConsumerChain(ctx, &mocks, prop.ChainId)...)
	}
	// Only first two consumer chains should be stopped
	expectations = append(expectations, testkeeper.GetMocksForStopConsumerChain(ctx, &mocks)...)
	expectations = append(expectations, testkeeper.GetMocksForStopConsumerChain(ctx, &mocks)...)

	gomock.InOrder(expectations...)

	//
	// Remaining setup
	//
	for _, prop := range pendingProps {
		// Setup a valid consumer chain for each prop
		additionProp := testkeeper.GetTestConsumerAdditionProp()
		additionProp.ChainId = prop.ChainId
		additionProp.InitialHeight = clienttypes.NewHeight(2, 3)
		err := providerKeeper.CreateConsumerClient(ctx, additionProp)
		require.NoError(t, err)
		err = providerKeeper.SetConsumerChain(ctx, "channelID")
		require.NoError(t, err)

		// Set removal props for all consumer chains
		providerKeeper.SetPendingConsumerRemovalProp(ctx, prop)
	}

	// Add an invalid prop to the store with an non-existing chain id
	invalidProp := ccvtypes.NewConsumerRemovalProposal(
		"title", "description", "chain4", now.Add(-time.Hour).UTC(),
	).(*ccvtypes.ConsumerRemovalProposal)
	providerKeeper.SetPendingConsumerRemovalProp(ctx, invalidProp)

	//
	// Test execution
	//
	providerKeeper.BeginBlockCCR(ctx)

	// Only the 3rd (final) proposal is still stored as pending
	found := providerKeeper.PendingConsumerRemovalPropExists(
		ctx, pendingProps[0].ChainId, pendingProps[0].StopTime)
	require.False(t, found)
	found = providerKeeper.PendingConsumerRemovalPropExists(
		ctx, pendingProps[1].ChainId, pendingProps[1].StopTime)
	require.False(t, found)
	found = providerKeeper.PendingConsumerRemovalPropExists(
		ctx, pendingProps[2].ChainId, pendingProps[2].StopTime)
	require.True(t, found)
	found = providerKeeper.PendingConsumerRemovalPropExists(
		ctx, invalidProp.ChainId, invalidProp.StopTime)
	require.False(t, found)
}

func TestHandleEquivocationProposal(t *testing.T) {
	equivocations := []*evidencetypes.Equivocation{
		{
			Time:             time.Now(),
			Height:           1,
			Power:            1,
			ConsensusAddress: "cosmosvalcons1kswr5sq599365kcjmhgufevfps9njf43e4lwdk",
		},
		{
			Time:             time.Now(),
			Height:           1,
			Power:            1,
			ConsensusAddress: "cosmosvalcons1ezyrq65s3gshhx5585w6mpusq3xsj3ayzf4uv6",
		},
	}

	prop := &ccvtypes.EquivocationProposal{
		Equivocations: []*evidencetypes.Equivocation{equivocations[0], equivocations[1]},
	}

	testCases := []struct {
		name                string
		setSlashLogs        bool
		expectEquivsHandled bool
		expectErr           bool
	}{
		{name: "slash logs not set", setSlashLogs: false, expectEquivsHandled: false, expectErr: true},
		{name: "slash logs set", setSlashLogs: true, expectEquivsHandled: true, expectErr: false},
	}
	for _, tc := range testCases {

		keeperParams := testkeeper.NewInMemKeeperParams(t)
		keeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, keeperParams)

		if tc.setSlashLogs {
			// Set slash logs according to cons addrs in equivocations
			consAddr := equivocations[0].GetConsensusAddress()
			require.NotNil(t, consAddr, "consensus address could not be parsed")
			keeper.SetSlashLog(ctx, ccvtypes.NewProviderConsAddress(consAddr))
			consAddr = equivocations[1].GetConsensusAddress()
			require.NotNil(t, consAddr, "consensus address could not be parsed")
			keeper.SetSlashLog(ctx, ccvtypes.NewProviderConsAddress(consAddr))
		}

		if tc.expectEquivsHandled {
			mocks.MockEvidenceKeeper.EXPECT().HandleEquivocationEvidence(ctx, equivocations[0])
			mocks.MockEvidenceKeeper.EXPECT().HandleEquivocationEvidence(ctx, equivocations[1])
		}

		err := keeper.HandleEquivocationProposal(ctx, prop)

		if tc.expectErr {
			require.Error(t, err)
		} else {
			require.NoError(t, err)
		}
		ctrl.Finish()
	}
}
