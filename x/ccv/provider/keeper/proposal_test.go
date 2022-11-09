package keeper_test

import (
	"encoding/json"
	"testing"
	"time"

	_go "github.com/confio/ics23/go"
	sdk "github.com/cosmos/cosmos-sdk/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	"github.com/golang/mock/gomock"
	abci "github.com/tendermint/tendermint/abci/types"

	"github.com/stretchr/testify/require"

	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	providerkeeper "github.com/cosmos/interchain-security/x/ccv/provider/keeper"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"
)

//
// Initialization sub-protocol related tests of proposal.go
//

// Tests the HandleConsumerAdditionProposal method against the SpawnConsumerChainProposalHandler spec.
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-spccprop1
// Spec tag: [CCV-PCF-SPCCPROP.1]
func TestHandleConsumerAdditionProposal(t *testing.T) {

	type testCase struct {
		description string
		prop        *providertypes.ConsumerAdditionProposal
		// Time when prop is handled
		blockTime time.Time
		// Whether it's expected that the spawn time has passed and client should be created
		expCreatedClient bool
	}

	// Snapshot times asserted in tests
	now := time.Now().UTC()
	hourFromNow := now.Add(time.Hour).UTC()

	tests := []testCase{
		{
			description: "ctx block time is after proposal's spawn time, expected that client is created",
			prop: providertypes.NewConsumerAdditionProposal(
				"title",
				"description",
				"chainID",
				clienttypes.NewHeight(2, 3),
				[]byte("gen_hash"),
				[]byte("bin_hash"),
				now, // Spawn time
			).(*providertypes.ConsumerAdditionProposal),
			blockTime:        hourFromNow,
			expCreatedClient: true,
		},
		{
			description: `ctx block time is before proposal's spawn time,
			 expected that no client is created and the proposal is persisted as pending`,
			prop: providertypes.NewConsumerAdditionProposal(
				"title",
				"description",
				"chainID",
				clienttypes.NewHeight(2, 3),
				[]byte("gen_hash"),
				[]byte("bin_hash"),
				hourFromNow, // Spawn time
			).(*types.ConsumerAdditionProposal),
			blockTime:        now,
			expCreatedClient: false,
		},
	}

	for _, tc := range tests {
		// Common setup
		keeperParams := testkeeper.NewInMemKeeperParams(t)
		providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, keeperParams)
		providerKeeper.SetParams(ctx, providertypes.DefaultParams())
		ctx = ctx.WithBlockTime(tc.blockTime)

		if tc.expCreatedClient {
			// Mock calls are only asserted if we expect a client to be created.
			gomock.InOrder(
				testkeeper.GetMocksForCreateConsumerClient(ctx, &mocks, "chainID", clienttypes.NewHeight(2, 3))...,
			)
		}

		tc.prop.LockUnbondingOnTimeout = false // Full functionality not implemented yet.

		err := providerKeeper.HandleConsumerAdditionProposal(ctx, tc.prop)
		require.NoError(t, err)

		if tc.expCreatedClient {
			testCreatedConsumerClient(t, ctx, providerKeeper, tc.prop.ChainId, "clientID")
		} else {
			// check that stored pending prop is exactly the same as the initially instantiated prop
			gotProposal, found := providerKeeper.GetPendingConsumerAdditionProp(ctx, tc.prop.SpawnTime, tc.prop.ChainId)
			require.True(t, found)
			require.Equal(t, *tc.prop, gotProposal)
			// double check that a client for this chain does not exist
			_, found = providerKeeper.GetConsumerClientId(ctx, tc.prop.ChainId)
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
		providerKeeper.SetParams(ctx, providertypes.DefaultParams())

		// Test specific setup
		tc.setup(&providerKeeper, ctx, &mocks)

		// Call method with same arbitrary values as defined above in mock expectations.
		err := providerKeeper.CreateConsumerClient(
			ctx, "chainID", clienttypes.NewHeight(4, 5), false) // LockUbdOnTimeout always false for now

		require.NoError(t, err)

		if tc.expClientCreated {
			testCreatedConsumerClient(t, ctx, providerKeeper, "chainID", "clientID")
		}

		// Assert mock calls from setup functions
		ctrl.Finish()
	}
}

// Executes test assertions for a created consumer client.
//
// Note: Separated from TestCreateConsumerClient to also be called from TestCreateConsumerChainProposal.
func testCreatedConsumerClient(t *testing.T,
	ctx sdk.Context, providerKeeper providerkeeper.Keeper, expectedChainID string, expectedClientID string) {

	// ClientID should be stored.
	clientId, found := providerKeeper.GetConsumerClientId(ctx, expectedChainID)
	require.True(t, found, "consumer client not found")
	require.Equal(t, expectedClientID, clientId)

	// Lock unbonding on timeout flag always false for now.
	lockUbdOnTimeout := providerKeeper.GetLockUnbondingOnTimeout(ctx, expectedChainID)
	require.False(t, lockUbdOnTimeout)

	// Only assert that consumer genesis was set,
	// more granular tests on consumer genesis should be defined in TestMakeConsumerGenesis
	_, ok := providerKeeper.GetConsumerGenesis(ctx, expectedChainID)
	require.True(t, ok)
}

// TestPendingConsumerAdditionPropDeletion tests the getting/setting
// and deletion keeper methods for pending consumer addition props
func TestPendingConsumerAdditionPropDeletion(t *testing.T) {

	testCases := []struct {
		types.ConsumerAdditionProposal
		ExpDeleted bool
	}{
		{
			ConsumerAdditionProposal: types.ConsumerAdditionProposal{ChainId: "0", SpawnTime: time.Now().UTC()},
			ExpDeleted:               true,
		},
		{
			ConsumerAdditionProposal: types.ConsumerAdditionProposal{ChainId: "1", SpawnTime: time.Now().UTC().Add(time.Hour)},
			ExpDeleted:               false,
		},
	}
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	for _, tc := range testCases {
		err := providerKeeper.SetPendingConsumerAdditionProp(ctx, &tc.ConsumerAdditionProposal)
		require.NoError(t, err)
	}

	ctx = ctx.WithBlockTime(time.Now().UTC())

	propsToExecute := providerKeeper.ConsumerAdditionPropsToExecute(ctx)
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

// TestPendingConsumerAdditionPropOrder tests that pending consumer addition proposals
// are accessed in order by timestamp via the iterator
func TestPendingConsumerAdditionPropOrder(t *testing.T) {

	now := time.Now().UTC()

	// props with unique chain ids and spawn times
	sampleProp1 := types.ConsumerAdditionProposal{ChainId: "1", SpawnTime: now}
	sampleProp2 := types.ConsumerAdditionProposal{ChainId: "2", SpawnTime: now.Add(1 * time.Hour)}
	sampleProp3 := types.ConsumerAdditionProposal{ChainId: "3", SpawnTime: now.Add(2 * time.Hour)}
	sampleProp4 := types.ConsumerAdditionProposal{ChainId: "4", SpawnTime: now.Add(3 * time.Hour)}
	sampleProp5 := types.ConsumerAdditionProposal{ChainId: "5", SpawnTime: now.Add(4 * time.Hour)}

	testCases := []struct {
		propSubmitOrder      []types.ConsumerAdditionProposal
		accessTime           time.Time
		expectedOrderedProps []types.ConsumerAdditionProposal
	}{
		{
			propSubmitOrder: []types.ConsumerAdditionProposal{
				sampleProp1, sampleProp2, sampleProp3, sampleProp4, sampleProp5,
			},
			accessTime: now.Add(30 * time.Minute),
			expectedOrderedProps: []types.ConsumerAdditionProposal{
				sampleProp1,
			},
		},
		{
			propSubmitOrder: []types.ConsumerAdditionProposal{
				sampleProp3, sampleProp2, sampleProp1, sampleProp5, sampleProp4,
			},
			accessTime: now.Add(3 * time.Hour).Add(30 * time.Minute),
			expectedOrderedProps: []types.ConsumerAdditionProposal{
				sampleProp1, sampleProp2, sampleProp3, sampleProp4,
			},
		},
		{
			propSubmitOrder: []types.ConsumerAdditionProposal{
				sampleProp5, sampleProp4, sampleProp3, sampleProp2, sampleProp1,
			},
			accessTime: now.Add(5 * time.Hour),
			expectedOrderedProps: []types.ConsumerAdditionProposal{
				sampleProp1, sampleProp2, sampleProp3, sampleProp4, sampleProp5,
			},
		},
	}

	for _, tc := range testCases {
		providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
		defer ctrl.Finish()

		ctx = ctx.WithBlockTime(tc.accessTime)

		for _, prop := range tc.propSubmitOrder {
			err := providerKeeper.SetPendingConsumerAdditionProp(ctx, &prop)
			require.NoError(t, err)
		}
		propsToExecute := providerKeeper.ConsumerAdditionPropsToExecute(ctx)
		require.Equal(t, tc.expectedOrderedProps, propsToExecute)
	}
}

//
// Consumer Chain Removal sub-protocol related tests of proposal.go
//

// TestHandleConsumerRemovalProposal tests HandleConsumerRemovalProposal against its corresponding spec method.
//
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-stccprop1
// Spec tag: [CCV-PCF-STCCPROP.1]
func TestHandleConsumerRemovalProposal(t *testing.T) {

	type testCase struct {
		description string
		// Consumer removal proposal to handle
		prop *types.ConsumerRemovalProposal
		// Time when prop is handled
		blockTime time.Time
		// Whether consumer chain should have been stopped
		expStop bool
	}

	// Snapshot times asserted in tests
	now := time.Now().UTC()
	hourFromNow := now.Add(time.Hour).UTC()

	tests := []testCase{
		{
			description: "valid proposal: stop time reached",
			prop: providertypes.NewConsumerRemovalProposal(
				"title",
				"description",
				"chainID",
				now,
			).(*providertypes.ConsumerRemovalProposal),
			blockTime: hourFromNow, // After stop time.
			expStop:   true,
		},
		{
			description: "valid proposal: stop time has not yet been reached",
			prop: providertypes.NewConsumerRemovalProposal(
				"title",
				"description",
				"chainID",
				hourFromNow,
			).(*providertypes.ConsumerRemovalProposal),
			blockTime: now, // Before proposal's stop time
			expStop:   false,
		},
	}

	for _, tc := range tests {

		// Common setup
		keeperParams := testkeeper.NewInMemKeeperParams(t)
		providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, keeperParams)
		providerKeeper.SetParams(ctx, providertypes.DefaultParams())
		ctx = ctx.WithBlockTime(tc.blockTime)

		// Mock expectations and setup for stopping the consumer chain, if applicable
		if tc.expStop {
			testkeeper.SetupForStoppingConsumerChain(t, ctx, &providerKeeper, mocks)
		}
		// Note: when expStop is false, no mocks are setup,
		// meaning no external keeper methods are allowed to be called.

		err := providerKeeper.HandleConsumerRemovalProposal(ctx, tc.prop)
		require.NoError(t, err)

		if tc.expStop {
			// Expect no pending proposal to exist
			found := providerKeeper.GetPendingConsumerRemovalProp(ctx, tc.prop.ChainId, tc.prop.StopTime)
			require.False(t, found)

			testProviderStateIsCleaned(t, ctx, providerKeeper, tc.prop.ChainId, "channelID")
		} else {
			// Proposal should be stored as pending
			found := providerKeeper.GetPendingConsumerRemovalProp(ctx, tc.prop.ChainId, tc.prop.StopTime)
			require.True(t, found)
		}

		// Assert mock calls from setup function
		ctrl.Finish()
	}
}

// Tests the StopConsumerChain method against the spec,
// with more granularity than what's covered in TestHandleConsumerRemovalProposal, or e2e tests.
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
			description: "fail due to an invalid unbonding index",
			setup: func(ctx sdk.Context, providerKeeper *providerkeeper.Keeper, mocks testkeeper.MockedKeepers) {
				// set invalid unbonding op index
				providerKeeper.SetUnbondingOpIndex(ctx, "chainID", 0, []uint64{0})

				// StopConsumerChain should return error, but state is still cleaned (asserted with mocks).
				testkeeper.SetupForStoppingConsumerChain(t, ctx, providerKeeper, mocks)
			},
			expErr: true,
		},
		{
			description: "proposal dropped, client doesn't exist",
			setup: func(ctx sdk.Context, providerKeeper *providerkeeper.Keeper, mocks testkeeper.MockedKeepers) {
				// No mocks, meaning no external keeper methods are allowed to be called.
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
		providerKeeper.SetParams(ctx, providertypes.DefaultParams())

		// Setup specific to test case
		tc.setup(ctx, &providerKeeper, mocks)

		err := providerKeeper.StopConsumerChain(ctx, "chainID", false, true)

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
	expectedChainID string, expectedChannelID string) {

	_, found := providerKeeper.GetConsumerClientId(ctx, expectedChainID)
	require.False(t, found)
	found = providerKeeper.GetLockUnbondingOnTimeout(ctx, expectedChainID)
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
	found = false
	providerKeeper.IterateVscSendTimestamps(ctx, expectedChainID, func(_ uint64, _ time.Time) bool {
		found = true
		return false
	})
	require.False(t, found)
}

// TestPendingConsumerRemovalPropDeletion tests the getting/setting
// and deletion methods for pending consumer removal props
func TestPendingConsumerRemovalPropDeletion(t *testing.T) {

	testCases := []struct {
		types.ConsumerRemovalProposal
		ExpDeleted bool
	}{
		{
			ConsumerRemovalProposal: types.ConsumerRemovalProposal{ChainId: "8", StopTime: time.Now().UTC()},
			ExpDeleted:              true,
		},
		{
			ConsumerRemovalProposal: types.ConsumerRemovalProposal{ChainId: "9", StopTime: time.Now().UTC().Add(time.Hour)},
			ExpDeleted:              false,
		},
	}
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	for _, tc := range testCases {
		providerKeeper.SetPendingConsumerRemovalProp(ctx, tc.ChainId, tc.StopTime)
	}

	ctx = ctx.WithBlockTime(time.Now().UTC())

	propsToExecute := providerKeeper.ConsumerRemovalPropsToExecute(ctx)
	// Delete consumer removal proposals, same as what would be done by BeginBlockCCR
	providerKeeper.DeletePendingConsumerRemovalProps(ctx, propsToExecute...)
	numDeleted := 0
	for _, tc := range testCases {
		res := providerKeeper.GetPendingConsumerRemovalProp(ctx, tc.ChainId, tc.StopTime)
		if !tc.ExpDeleted {
			require.NotEmpty(t, res, "consumer removal prop was deleted: %s %s", tc.ChainId, tc.StopTime.String())
			continue
		}
		require.Empty(t, res, "consumer removal prop was not deleted %s %s", tc.ChainId, tc.StopTime.String())
		require.Equal(t, propsToExecute[numDeleted].ChainId, tc.ChainId)
		numDeleted += 1
	}
}

// Tests that pending consumer removal proposals are accessed in order by timestamp via the iterator
func TestPendingConsumerRemovalPropOrder(t *testing.T) {

	now := time.Now().UTC()

	// props with unique chain ids and spawn times
	sampleProp1 := types.ConsumerRemovalProposal{ChainId: "1", StopTime: now}
	sampleProp2 := types.ConsumerRemovalProposal{ChainId: "2", StopTime: now.Add(1 * time.Hour)}
	sampleProp3 := types.ConsumerRemovalProposal{ChainId: "3", StopTime: now.Add(2 * time.Hour)}
	sampleProp4 := types.ConsumerRemovalProposal{ChainId: "4", StopTime: now.Add(3 * time.Hour)}
	sampleProp5 := types.ConsumerRemovalProposal{ChainId: "5", StopTime: now.Add(4 * time.Hour)}

	testCases := []struct {
		propSubmitOrder      []types.ConsumerRemovalProposal
		accessTime           time.Time
		expectedOrderedProps []types.ConsumerRemovalProposal
	}{
		{
			propSubmitOrder: []types.ConsumerRemovalProposal{
				sampleProp1, sampleProp2, sampleProp3, sampleProp4, sampleProp5,
			},
			accessTime: now.Add(30 * time.Minute),
			expectedOrderedProps: []types.ConsumerRemovalProposal{
				sampleProp1,
			},
		},
		{
			propSubmitOrder: []types.ConsumerRemovalProposal{
				sampleProp3, sampleProp2, sampleProp1, sampleProp5, sampleProp4,
			},
			accessTime: now.Add(3 * time.Hour).Add(30 * time.Minute),
			expectedOrderedProps: []types.ConsumerRemovalProposal{
				sampleProp1, sampleProp2, sampleProp3, sampleProp4,
			},
		},
		{
			propSubmitOrder: []types.ConsumerRemovalProposal{
				sampleProp5, sampleProp4, sampleProp3, sampleProp2, sampleProp1,
			},
			accessTime: now.Add(5 * time.Hour),
			expectedOrderedProps: []types.ConsumerRemovalProposal{
				sampleProp1, sampleProp2, sampleProp3, sampleProp4, sampleProp5,
			},
		},
	}

	for _, tc := range testCases {
		providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
		defer ctrl.Finish()
		ctx = ctx.WithBlockTime(tc.accessTime)

		for _, prop := range tc.propSubmitOrder {
			providerKeeper.SetPendingConsumerRemovalProp(ctx, prop.ChainId, prop.StopTime)
		}
		propsToExecute := providerKeeper.ConsumerRemovalPropsToExecute(ctx)
		require.Equal(t, tc.expectedOrderedProps, propsToExecute)
	}
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
		TrustingPeriodFraction: providertypes.DefaultTrustingPeriodFraction,
		CcvTimeoutPeriod:       ccvtypes.DefaultCCVTimeoutPeriod,
		InitTimeoutPeriod:      types.DefaultInitTimeoutPeriod,
		VscTimeoutPeriod:       types.DefaultVscTimeoutPeriod,
	}
	providerKeeper.SetParams(ctx, moduleParams)
	defer ctrl.Finish()

	//
	// Other setup not covered by custom template client state
	//
	ctx = ctx.WithChainID("testchain1") // chainID is obtained from ctx
	ctx = ctx.WithBlockHeight(5)        // RevisionHeight obtained from ctx
	gomock.InOrder(testkeeper.GetMocksForMakeConsumerGenesis(ctx, &mocks, 1814400000000000)...)

	actualGenesis, err := providerKeeper.MakeConsumerGenesis(ctx)
	require.NoError(t, err)

	jsonString := `{"params":{"enabled":true, "blocks_per_distribution_transmission":1000, "ccv_timeout_period":2419200000000000, "transfer_timeout_period": 3600000000000, "consumer_redistribution_fraction":"0.75", "historical_entries":10000, "unbonding_period": 1728000000000000},"new_chain":true,"provider_client_state":{"chain_id":"testchain1","trust_level":{"numerator":1,"denominator":3},"trusting_period":907200000000000,"unbonding_period":1814400000000000,"max_clock_drift":10000000000,"frozen_height":{},"latest_height":{"revision_height":5},"proof_specs":[{"leaf_spec":{"hash":1,"prehash_value":1,"length":1,"prefix":"AA=="},"inner_spec":{"child_order":[0,1],"child_size":33,"min_prefix_length":4,"max_prefix_length":12,"hash":1}},{"leaf_spec":{"hash":1,"prehash_value":1,"length":1,"prefix":"AA=="},"inner_spec":{"child_order":[0,1],"child_size":32,"min_prefix_length":1,"max_prefix_length":1,"hash":1}}],"upgrade_path":["upgrade","upgradedIBCState"],"allow_update_after_expiry":true,"allow_update_after_misbehaviour":true},"provider_consensus_state":{"timestamp":"2020-01-02T00:00:10Z","root":{"hash":"LpGpeyQVLUo9HpdsgJr12NP2eCICspcULiWa5u9udOA="},"next_validators_hash":"E30CE736441FB9101FADDAF7E578ABBE6DFDB67207112350A9A904D554E1F5BE"},"unbonding_sequences":null,"initial_val_set":[{"pub_key":{"type":"tendermint/PubKeyEd25519","value":"dcASx5/LIKZqagJWN0frOlFtcvz91frYmj/zmoZRWro="},"power":1}]}`

	var expectedGenesis consumertypes.GenesisState
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
	providerKeeper.SetParams(ctx, providertypes.DefaultParams())
	defer ctrl.Finish()
	ctx = ctx.WithBlockTime(now)

	pendingProps := []*providertypes.ConsumerAdditionProposal{
		providertypes.NewConsumerAdditionProposal(
			"title", "description", "chain1", clienttypes.NewHeight(3, 4), []byte{}, []byte{},
			now.Add(-time.Hour).UTC()).(*providertypes.ConsumerAdditionProposal),
		providertypes.NewConsumerAdditionProposal(
			"title", "description", "chain2", clienttypes.NewHeight(3, 4), []byte{}, []byte{},
			now.UTC()).(*providertypes.ConsumerAdditionProposal),
		providertypes.NewConsumerAdditionProposal(
			"title", "description", "chain3", clienttypes.NewHeight(3, 4), []byte{}, []byte{},
			now.Add(time.Hour).UTC()).(*providertypes.ConsumerAdditionProposal),
	}

	gomock.InOrder(
		// Expect client creation for the 1st and second proposals (spawn time already passed)
		append(testkeeper.GetMocksForCreateConsumerClient(ctx, &mocks, "chain1", clienttypes.NewHeight(3, 4)),
			testkeeper.GetMocksForCreateConsumerClient(ctx, &mocks, "chain2", clienttypes.NewHeight(3, 4))...)...,
	)

	for _, prop := range pendingProps {
		err := providerKeeper.SetPendingConsumerAdditionProp(ctx, prop)
		require.NoError(t, err)
	}

	providerKeeper.BeginBlockInit(ctx)

	// Only the 3rd (final) proposal is still stored as pending
	_, found := providerKeeper.GetPendingConsumerAdditionProp(
		ctx, pendingProps[0].SpawnTime, pendingProps[0].ChainId)
	require.False(t, found)
	_, found = providerKeeper.GetPendingConsumerAdditionProp(
		ctx, pendingProps[1].SpawnTime, pendingProps[1].ChainId)
	require.False(t, found)
	_, found = providerKeeper.GetPendingConsumerAdditionProp(
		ctx, pendingProps[2].SpawnTime, pendingProps[2].ChainId)
	require.True(t, found)
}

// TestBeginBlockCCR tests BeginBlockCCR against the spec.
//
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-bblock-ccr1
// Spec tag: [CCV-PCF-BBLOCK-CCR.1]
func TestBeginBlockCCR(t *testing.T) {
	now := time.Now().UTC()

	keeperParams := testkeeper.NewInMemKeeperParams(t)
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, keeperParams)
	providerKeeper.SetParams(ctx, providertypes.DefaultParams())
	defer ctrl.Finish()
	ctx = ctx.WithBlockTime(now)

	pendingProps := []*providertypes.ConsumerRemovalProposal{
		providertypes.NewConsumerRemovalProposal(
			"title", "description", "chain1", now.Add(-time.Hour).UTC(),
		).(*providertypes.ConsumerRemovalProposal),
		providertypes.NewConsumerRemovalProposal(
			"title", "description", "chain2", now,
		).(*providertypes.ConsumerRemovalProposal),
		providertypes.NewConsumerRemovalProposal(
			"title", "description", "chain3", now.Add(time.Hour).UTC(),
		).(*providertypes.ConsumerRemovalProposal),
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
		err := providerKeeper.CreateConsumerClient(ctx, prop.ChainId, clienttypes.NewHeight(2, 3), false)
		require.NoError(t, err)
		err = providerKeeper.SetConsumerChain(ctx, "channelID")
		require.NoError(t, err)

		// Set removal props for all consumer chains
		providerKeeper.SetPendingConsumerRemovalProp(ctx, prop.ChainId, prop.StopTime)
	}

	//
	// Test execution
	//
	providerKeeper.BeginBlockCCR(ctx)

	// Only the 3rd (final) proposal is still stored as pending
	found := providerKeeper.GetPendingConsumerRemovalProp(
		ctx, pendingProps[0].ChainId, pendingProps[0].StopTime)
	require.False(t, found)
	found = providerKeeper.GetPendingConsumerRemovalProp(
		ctx, pendingProps[1].ChainId, pendingProps[1].StopTime)
	require.False(t, found)
	found = providerKeeper.GetPendingConsumerRemovalProp(
		ctx, pendingProps[2].ChainId, pendingProps[2].StopTime)
	require.True(t, found)
}

// Test getting both matured and pending comnsumer addition proposals
func TestGetAllConsumerAdditionProps(t *testing.T) {
	now := time.Now().UTC()

	props := []types.ConsumerAdditionProposal{
		{ChainId: "1", SpawnTime: now.Add(1 * time.Hour)},
		{ChainId: "2", SpawnTime: now.Add(2 * time.Hour)},
		{ChainId: "3", SpawnTime: now.Add(3 * time.Hour)},
		{ChainId: "4", SpawnTime: now.Add(4 * time.Hour)},
	}

	keeperParams := testkeeper.NewInMemKeeperParams(t)
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, keeperParams)
	defer ctrl.Finish()

	for _, prop := range props {
		cpProp := prop // bring into loop scope - avoids using iterator pointer instead of value pointer
		err := providerKeeper.SetPendingConsumerAdditionProp(ctx, &cpProp)
		require.NoError(t, err)
	}

	// advance the clock to be 1 minute after first proposal
	ctx = ctx.WithBlockTime(now.Add(time.Minute))
	res := providerKeeper.GetAllConsumerAdditionProps(ctx)
	require.NotEmpty(t, res, "GetAllConsumerAdditionProps returned empty result")
	require.Len(t, res.Pending, 4, "wrong len for pending addition props")
	require.Equal(t, props[0].ChainId, res.Pending[0].ChainId, "wrong chain ID for pending addition prop")
}

// Test getting both matured and pending consumer removal proposals
func TestGetAllConsumerRemovalProps(t *testing.T) {
	now := time.Now().UTC()

	props := []types.ConsumerRemovalProposal{
		{ChainId: "1", StopTime: now.Add(1 * time.Hour)},
		{ChainId: "2", StopTime: now.Add(2 * time.Hour)},
		{ChainId: "3", StopTime: now.Add(3 * time.Hour)},
		{ChainId: "4", StopTime: now.Add(4 * time.Hour)},
	}

	keeperParams := testkeeper.NewInMemKeeperParams(t)
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, keeperParams)
	defer ctrl.Finish()

	for _, prop := range props {
		providerKeeper.SetPendingConsumerRemovalProp(ctx, prop.ChainId, prop.StopTime)
	}

	// advance the clock to be 1 minute after first proposal
	ctx = ctx.WithBlockTime(now.Add(time.Minute))
	res := providerKeeper.GetAllConsumerRemovalProps(ctx)
	require.NotEmpty(t, res, "GetAllConsumerRemovalProps returned empty result")
	require.Len(t, res.Pending, 4, "wrong len for pending removal props")
	require.Equal(t, props[0].ChainId, res.Pending[0].ChainId, "wrong chain ID for pending removal prop")
}
