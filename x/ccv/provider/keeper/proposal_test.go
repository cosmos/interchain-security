package keeper_test

import (
	"testing"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	capabilitytypes "github.com/cosmos/cosmos-sdk/x/capability/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	"github.com/golang/mock/gomock"

	"github.com/stretchr/testify/require"

	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	providerkeeper "github.com/cosmos/interchain-security/x/ccv/provider/keeper"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"

	extra "github.com/oxyno-zeta/gomock-extra-matcher"
)

// TODO(Shawn): Finish commenting all tests in this file

//
// Initialization sub-protocol related tests of proposal.go
//

// Tests the HandleCreateConsumerChainProposal method against the SpawnConsumerChainProposalHandler spec.
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-spccprop1
// Spec tag: [CCV-PCF-SPCCPROP.1]
func TestHandleCreateConsumerChainProposal(t *testing.T) {

	const (
		// Value to inject into mocked returned value for CreateClient in each test case
		clientIDToInject = "clientID"
	)

	type testCase struct {
		description string
		prop        *providertypes.CreateConsumerChainProposal
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
			prop: providertypes.NewCreateConsumerChainProposal(
				"title",
				"description",
				"chainID",
				clienttypes.NewHeight(2, 3),
				[]byte("gen_hash"),
				[]byte("bin_hash"),
				now, // Spawn time
			).(*providertypes.CreateConsumerChainProposal),
			blockTime:        hourFromNow,
			expCreatedClient: true,
		},
		{
			description: `ctx block time is before proposal's spawn time,
			 expected that no client is created and the proposal is persisted as pending`,
			prop: providertypes.NewCreateConsumerChainProposal(
				"title",
				"description",
				"chainID",
				clienttypes.NewHeight(2, 3),
				[]byte("gen_hash"),
				[]byte("bin_hash"),
				hourFromNow, // Spawn time
			).(*types.CreateConsumerChainProposal),
			blockTime:        now,
			expCreatedClient: false,
		},
	}

	for _, tc := range tests {

		// Keeper is setup in the same way whether the tested proposal is expected to be stored as pending
		// or not. Mock calls however, are only asserted if we expect a client to be created.
		ctx, ctrl, providerKeeper, mockClientKeeper, mockStakingKeeper := setupKeeper(t)

		ctx = ctx.WithBlockTime(tc.blockTime)

		if tc.expCreatedClient {
			setupMocksForClientCreation(ctx, providerKeeper, mockClientKeeper, mockStakingKeeper,
				tc.prop.ChainId, tc.prop.InitialHeight, clientIDToInject)
		}

		tc.prop.LockUnbondingOnTimeout = false // Full functionality not implemented yet.

		err := providerKeeper.HandleCreateConsumerChainProposal(ctx, tc.prop)
		require.NoError(t, err)

		if tc.expCreatedClient {
			testCreatedConsumerClient(t, ctx, providerKeeper, tc.prop.ChainId, clientIDToInject)
		} else {
			// check that stored pending prop is exactly the same as the initially instantiated prop
			gotProposal := providerKeeper.GetPendingCreateProposal(ctx, tc.prop.SpawnTime, tc.prop.ChainId)
			require.Equal(t, *tc.prop, gotProposal)
			// double check that a client for this chain does not exist
			_, found := providerKeeper.GetConsumerClientId(ctx, tc.prop.ChainId)
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

	// Arbitrary values used in the following tests and assertions
	const (
		arbitraryClientID = "clientID"
		arbitraryChainID  = "chainID"
		lockUbdOnTimeout  = false // Always set to false as is.
	)

	var (
		arbitraryLatestHeight = clienttypes.NewHeight(4, 5)
	)

	type testCase struct {
		description string
		// Any state-mutating setup specific to this test case
		testSetup func() (sdk.Context, *gomock.Controller, providerkeeper.Keeper)
		// Whether a client should be created
		expClientCreated bool
	}
	tests := []testCase{
		{
			description: "No odd state mutation, new client should be created",
			testSetup: func() (sdk.Context, *gomock.Controller, providerkeeper.Keeper) {

				ctx, ctrl, providerKeeper, mockClientKeeper, mockStakingKeeper := setupKeeper(t)

				// Valid client creation is asserted with mock expectations here
				setupMocksForClientCreation(ctx, providerKeeper, mockClientKeeper, mockStakingKeeper,
					arbitraryChainID, arbitraryLatestHeight, arbitraryClientID)

				return ctx, ctrl, providerKeeper
			},
			expClientCreated: true,
		},
		{
			description: "client for this chain already exists, new one is not created",
			testSetup: func() (sdk.Context, *gomock.Controller, providerkeeper.Keeper) {

				ctx, ctrl, providerKeeper, mockClientKeeper, mockStakingKeeper := setupKeeper(t)

				providerKeeper.SetConsumerClientId(ctx, arbitraryChainID, arbitraryClientID)

				// Expect none of the client creation related calls to happen
				mockStakingKeeper.EXPECT().UnbondingTime(gomock.Any()).Times(0)
				mockClientKeeper.EXPECT().CreateClient(gomock.Any(), gomock.Any(), gomock.Any()).Times(0)
				mockClientKeeper.EXPECT().GetSelfConsensusState(gomock.Any(), gomock.Any()).Times(0)
				mockStakingKeeper.EXPECT().IterateLastValidatorPowers(gomock.Any(), gomock.Any()).Times(0)

				return ctx, ctrl, providerKeeper
			},
			expClientCreated: false,
		},
	}

	for _, tc := range tests {
		// Setup
		ctx, ctrl, providerKeeper := tc.testSetup()

		// Call method with arbitrary const values defined above.
		err := providerKeeper.CreateConsumerClient(
			ctx, arbitraryChainID, arbitraryLatestHeight, lockUbdOnTimeout)

		require.NoError(t, err)

		if tc.expClientCreated {
			testCreatedConsumerClient(t, ctx, providerKeeper, arbitraryChainID, arbitraryClientID)
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

// Sets up mock call expectations for a consumer client being created.
func setupMocksForClientCreation(ctx sdk.Context, providerKeeper providerkeeper.Keeper,
	mockClientKeeper *testkeeper.MockClientKeeper,
	mockStakingKeeper *testkeeper.MockStakingKeeper,
	expectedChainID string, expectedLatestHeight clienttypes.Height, clientIDToInject string) {

	gomock.InOrder(
		mockStakingKeeper.EXPECT().UnbondingTime(ctx).Return(time.Hour).Times(
			1, // called once in CreateConsumerClient
		),

		mockClientKeeper.EXPECT().CreateClient(
			ctx,
			// Allows us to expect a match by field. These are the only two client state values
			// that are dependant on parameters passed to CreateConsumerClient.
			extra.StructMatcher().Field(
				"ChainId", expectedChainID).Field(
				"LatestHeight", expectedLatestHeight,
			),
			gomock.Any(),
		).Return(clientIDToInject, nil).Times(1),

		mockStakingKeeper.EXPECT().UnbondingTime(ctx).Return(time.Hour).Times(
			1, // called again in MakeConsumerGenesis
		),

		mockClientKeeper.EXPECT().GetSelfConsensusState(ctx,
			clienttypes.GetSelfHeight(ctx)).Return(&ibctmtypes.ConsensusState{}, nil).Times(1),

		mockStakingKeeper.EXPECT().IterateLastValidatorPowers(ctx, gomock.Any()).Times(1),
	)
}

// Sets up keepers in a way that's common to testing proposals and client creation in this file.
func setupKeeper(t *testing.T) (
	sdk.Context, *gomock.Controller, providerkeeper.Keeper,
	*testkeeper.MockClientKeeper, *testkeeper.MockStakingKeeper) {

	// TODO: Use the refactored unit test helpers, then maybe this method wont be needed anymore

	ctrl := gomock.NewController(t)
	cdc, storeKey, paramsSubspace, ctx := testkeeper.SetupInMemKeeper(t)

	testkeeper.SetTemplateClientState(ctx, &paramsSubspace)

	mockClientKeeper := testkeeper.NewMockClientKeeper(ctrl)
	mockStakingKeeper := testkeeper.NewMockStakingKeeper(ctrl)

	providerKeeper := testkeeper.GetProviderKeeperWithMocks(
		cdc,
		storeKey,
		paramsSubspace,
		testkeeper.NewMockScopedKeeper(ctrl),
		testkeeper.NewMockChannelKeeper(ctrl),
		testkeeper.NewMockPortKeeper(ctrl),
		testkeeper.NewMockConnectionKeeper(ctrl),
		mockClientKeeper,
		mockStakingKeeper,
		testkeeper.NewMockSlashingKeeper(ctrl),
		testkeeper.NewMockAccountKeeper(ctrl),
	)
	return ctx, ctrl, providerKeeper, mockClientKeeper, mockStakingKeeper
}

func TestPendingCreateProposalsDeletion(t *testing.T) {

	testCases := []struct {
		types.CreateConsumerChainProposal
		ExpDeleted bool
	}{
		{
			CreateConsumerChainProposal: types.CreateConsumerChainProposal{ChainId: "0", SpawnTime: time.Now().UTC()},
			ExpDeleted:                  true,
		},
		{
			CreateConsumerChainProposal: types.CreateConsumerChainProposal{ChainId: "1", SpawnTime: time.Now().UTC().Add(time.Hour)},
			ExpDeleted:                  false,
		},
	}
	providerKeeper, ctx := testkeeper.GetProviderKeeperAndCtx(t)

	for _, tc := range testCases {
		err := providerKeeper.SetPendingCreateProposal(ctx, &tc.CreateConsumerChainProposal)
		require.NoError(t, err)
	}

	ctx = ctx.WithBlockTime(time.Now().UTC())

	propsToExecute := providerKeeper.CreateProposalsToExecute(ctx)
	// Delete create proposals, same as what would be done by IteratePendingCreateProposal
	providerKeeper.DeletePendingCreateProposal(ctx, propsToExecute...)
	numDeleted := 0
	for _, tc := range testCases {
		res := providerKeeper.GetPendingCreateProposal(ctx, tc.SpawnTime, tc.ChainId)
		if !tc.ExpDeleted {
			require.NotEmpty(t, res, "create proposal was deleted: %s %s", tc.ChainId, tc.SpawnTime.String())
			continue
		}
		require.Empty(t, res, "create proposal was not deleted %s %s", tc.ChainId, tc.SpawnTime.String())
		require.Equal(t, propsToExecute[numDeleted].ChainId, tc.ChainId)
		numDeleted += 1
	}
}

// Tests that pending create proposals are accessed in order by timestamp via the iterator
func TestPendingCreateProposalsOrder(t *testing.T) {

	now := time.Now().UTC()

	// props with unique chain ids and spawn times
	sampleProp1 := types.CreateConsumerChainProposal{ChainId: "1", SpawnTime: now}
	sampleProp2 := types.CreateConsumerChainProposal{ChainId: "2", SpawnTime: now.Add(1 * time.Hour)}
	sampleProp3 := types.CreateConsumerChainProposal{ChainId: "3", SpawnTime: now.Add(2 * time.Hour)}
	sampleProp4 := types.CreateConsumerChainProposal{ChainId: "4", SpawnTime: now.Add(3 * time.Hour)}
	sampleProp5 := types.CreateConsumerChainProposal{ChainId: "5", SpawnTime: now.Add(4 * time.Hour)}

	testCases := []struct {
		propSubmitOrder      []types.CreateConsumerChainProposal
		accessTime           time.Time
		expectedOrderedProps []types.CreateConsumerChainProposal
	}{
		{
			propSubmitOrder: []types.CreateConsumerChainProposal{
				sampleProp1, sampleProp2, sampleProp3, sampleProp4, sampleProp5,
			},
			accessTime: now.Add(30 * time.Minute),
			expectedOrderedProps: []types.CreateConsumerChainProposal{
				sampleProp1,
			},
		},
		{
			propSubmitOrder: []types.CreateConsumerChainProposal{
				sampleProp3, sampleProp2, sampleProp1, sampleProp5, sampleProp4,
			},
			accessTime: now.Add(3 * time.Hour).Add(30 * time.Minute),
			expectedOrderedProps: []types.CreateConsumerChainProposal{
				sampleProp1, sampleProp2, sampleProp3, sampleProp4,
			},
		},
		{
			propSubmitOrder: []types.CreateConsumerChainProposal{
				sampleProp5, sampleProp4, sampleProp3, sampleProp2, sampleProp1,
			},
			accessTime: now.Add(5 * time.Hour),
			expectedOrderedProps: []types.CreateConsumerChainProposal{
				sampleProp1, sampleProp2, sampleProp3, sampleProp4, sampleProp5,
			},
		},
	}

	for _, tc := range testCases {
		providerKeeper, ctx := testkeeper.GetProviderKeeperAndCtx(t)
		ctx = ctx.WithBlockTime(tc.accessTime)

		for _, prop := range tc.propSubmitOrder {
			err := providerKeeper.SetPendingCreateProposal(ctx, &prop)
			require.NoError(t, err)
		}
		propsToExecute := providerKeeper.CreateProposalsToExecute(ctx)
		require.Equal(t, tc.expectedOrderedProps, propsToExecute)
	}
}

//
// Consumer Chain Removal sub-protocol related tests of proposal.go
//

func TestHandleConsumerRemovalProposal(t *testing.T) {

	type testCase struct {
		description string
		prop        *types.StopConsumerChainProposal
		// Any state-mutating setup specific to this test case
		testSetup func() (sdk.Context, *gomock.Controller, providerkeeper.Keeper,
			*testkeeper.MockClientKeeper, *testkeeper.MockStakingKeeper)
		// Time when prop is handled
		blockTime time.Time
		// Whether we should expect the method to return an error
		expErr bool
		// Whether consumer chain should have been stopped
		expStop bool
	}

	//
	// TODO: Merge unit test refactors into this PR, then continue below.
	// TODO: Need to have all keeper setup(s) defined in testSetup function, with returned values only
	// TODO: Make sure to cover everything that was covered before in the e2e test.
	//

	// Snapshot times asserted in tests
	now := time.Now().UTC()
	hourFromNow := now.Add(time.Hour).UTC()

	tests := []testCase{
		// TODO: Use prop constructor once refactors are done
		{
			description: "valid stop consumer chain proposal: stop time reached",
			prop: &providertypes.StopConsumerChainProposal{
				Title:       "title",
				Description: "description",
				ChainId:     "chainId",
				StopTime:    now,
			},
			testSetup: func() (sdk.Context, *gomock.Controller, providerkeeper.Keeper,
				*testkeeper.MockClientKeeper, *testkeeper.MockStakingKeeper) {
				ctx, ctrl, providerKeeper, mockClientKeeper, mockStakingKeeper := setupKeeper(t)
				return ctx, ctrl, providerKeeper, mockClientKeeper, mockStakingKeeper
			},
			blockTime: hourFromNow, // After stop time.
			expErr:    false,
			expStop:   true,
		},
		{
			description: "valid proposal: stop time has not yet been reached",
			prop: &providertypes.StopConsumerChainProposal{
				Title:       "title",
				Description: "description",
				ChainId:     "chainId",
				StopTime:    hourFromNow,
			},
			testSetup: func() (sdk.Context, *gomock.Controller, providerkeeper.Keeper,
				*testkeeper.MockClientKeeper, *testkeeper.MockStakingKeeper) {
				ctx, ctrl, providerKeeper, mockClientKeeper, mockStakingKeeper := setupKeeper(t)
				return ctx, ctrl, providerKeeper, mockClientKeeper, mockStakingKeeper
			},
			blockTime: now, // Before proposal's stop time
			expErr:    false,
			expStop:   false,
		},
		{
			description: "valid proposal: fail due to an invalid unbonding index",
			prop: &providertypes.StopConsumerChainProposal{
				Title:       "title",
				Description: "description",
				ChainId:     "chainId",
				StopTime:    now,
			},
			testSetup: func() (sdk.Context, *gomock.Controller, providerkeeper.Keeper,
				*testkeeper.MockClientKeeper, *testkeeper.MockStakingKeeper) {
				ctx, ctrl, providerKeeper, mockClientKeeper, mockStakingKeeper := setupKeeper(t)
				// set invalid unbonding op index
				providerKeeper.SetUnbondingOpIndex(ctx, "chainId", 0, []uint64{0})
				return ctx, ctrl, providerKeeper, mockClientKeeper, mockStakingKeeper
			},
			blockTime: hourFromNow,
			expErr:    true,
			expStop:   true,
		},
		// TODO: test case that client id already exists
	}

	for _, tc := range tests {

		// Common setup
		ctx, _, providerKeeper, mockClientKeeper, mockStakingKeeper := tc.testSetup()
		ctx = ctx.WithBlockTime(tc.blockTime)
		injectedClientID := "clientID"
		setupMocksForClientCreation(ctx, providerKeeper, mockClientKeeper, mockStakingKeeper,
			tc.prop.ChainId, clienttypes.NewHeight(2, 3), injectedClientID)
		providerKeeper.CreateConsumerClient(ctx, tc.prop.ChainId, clienttypes.NewHeight(2, 3), false)

		injectedChannelId := "channelID"
		// TODO Mock channel keeper

		err := providerKeeper.SetConsumerChain(ctx, injectedChannelId)
		require.NoError(t, err)
		// TODO: make better here after updating downstream
		setupMocksForClosingChannel(ctx, providerKeeper, nil, nil)

		err = providerKeeper.HandleStopConsumerChainProposal(ctx, tc.prop)

		if tc.expErr {
			require.NoError(t, err)
		} else {
			require.Error(t, err)
		}

		if tc.expStop {
			testStoppedConsumerChain(t, ctx, providerKeeper, tc.prop.ChainId, injectedChannelId)
		} else {
			// Proposal should be stored as pending
			found := providerKeeper.GetPendingStopProposal(ctx, tc.prop.ChainId, tc.prop.StopTime)
			require.True(t, found)
			// double check that a client for this chain does still exist
			_, found = providerKeeper.GetConsumerClientId(ctx, tc.prop.ChainId)
			require.True(t, found)
		}

		// Assert mock calls from setup functions
		// ctrl.Finish()
	}
}

// TODO: Test https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-stcc1
// Similar to the more granular test for CreateConsumerClient above. Test unbonding ops, etc.

// Executes test assertions for a stopped consumer chain.
//
// Note: Separated from TestStopConsumerChain to also be called from TestHandleConsumerRemovalProposal.
func testStoppedConsumerChain(t *testing.T, ctx sdk.Context, providerKeeper providerkeeper.Keeper,
	expectedChainID string, expectedChannelID string) {
	// Expect state to be cleaned.
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
	// TODO:  Mas around unbonding ops
}

// Sets up mock call expectations for a channel being closed.
func setupMocksForClosingChannel(ctx sdk.Context, providerKeeper providerkeeper.Keeper,
	mockChannelKeeper *testkeeper.MockChannelKeeper,
	mockScopedKeeper *testkeeper.MockScopedKeeper) {

	dummyCap := &capabilitytypes.Capability{}
	// TODO: might need to combine with previous expects
	gomock.InOrder(
		mockChannelKeeper.EXPECT().GetChannel(ctx, ccv.ProviderPortID,
			gomock.Any()).Return("channelID", true).Times(1),
		mockScopedKeeper.EXPECT().GetCapability(ctx, gomock.Any()).Return(dummyCap, true).Times(1),
		mockChannelKeeper.EXPECT().ChanCloseInit(ctx, ccv.ProviderPortID, "channelID", dummyCap),
	)
}

func TestPendingStopProposalDeletion(t *testing.T) {

	testCases := []struct {
		types.StopConsumerChainProposal
		ExpDeleted bool
	}{
		{
			StopConsumerChainProposal: types.StopConsumerChainProposal{ChainId: "8", StopTime: time.Now().UTC()},
			ExpDeleted:                true,
		},
		{
			StopConsumerChainProposal: types.StopConsumerChainProposal{ChainId: "9", StopTime: time.Now().UTC().Add(time.Hour)},
			ExpDeleted:                false,
		},
	}
	providerKeeper, ctx := testkeeper.GetProviderKeeperAndCtx(t)

	for _, tc := range testCases {
		providerKeeper.SetPendingStopProposal(ctx, tc.ChainId, tc.StopTime)
	}

	ctx = ctx.WithBlockTime(time.Now().UTC())

	propsToExecute := providerKeeper.StopProposalsToExecute(ctx)
	// Delete stop proposals, same as what would be done by IteratePendingStopProposal
	providerKeeper.DeletePendingStopProposals(ctx, propsToExecute...)
	numDeleted := 0
	for _, tc := range testCases {
		res := providerKeeper.GetPendingStopProposal(ctx, tc.ChainId, tc.StopTime)
		if !tc.ExpDeleted {
			require.NotEmpty(t, res, "stop proposal was deleted: %s %s", tc.ChainId, tc.StopTime.String())
			continue
		}
		require.Empty(t, res, "stop proposal was not deleted %s %s", tc.ChainId, tc.StopTime.String())
		require.Equal(t, propsToExecute[numDeleted].ChainId, tc.ChainId)
		numDeleted += 1
	}
}

// Tests that pending stop proposals are accessed in order by timestamp via the iterator
func TestPendingStopProposalsOrder(t *testing.T) {

	now := time.Now().UTC()

	// props with unique chain ids and spawn times
	sampleProp1 := types.StopConsumerChainProposal{ChainId: "1", StopTime: now}
	sampleProp2 := types.StopConsumerChainProposal{ChainId: "2", StopTime: now.Add(1 * time.Hour)}
	sampleProp3 := types.StopConsumerChainProposal{ChainId: "3", StopTime: now.Add(2 * time.Hour)}
	sampleProp4 := types.StopConsumerChainProposal{ChainId: "4", StopTime: now.Add(3 * time.Hour)}
	sampleProp5 := types.StopConsumerChainProposal{ChainId: "5", StopTime: now.Add(4 * time.Hour)}

	testCases := []struct {
		propSubmitOrder      []types.StopConsumerChainProposal
		accessTime           time.Time
		expectedOrderedProps []types.StopConsumerChainProposal
	}{
		{
			propSubmitOrder: []types.StopConsumerChainProposal{
				sampleProp1, sampleProp2, sampleProp3, sampleProp4, sampleProp5,
			},
			accessTime: now.Add(30 * time.Minute),
			expectedOrderedProps: []types.StopConsumerChainProposal{
				sampleProp1,
			},
		},
		{
			propSubmitOrder: []types.StopConsumerChainProposal{
				sampleProp3, sampleProp2, sampleProp1, sampleProp5, sampleProp4,
			},
			accessTime: now.Add(3 * time.Hour).Add(30 * time.Minute),
			expectedOrderedProps: []types.StopConsumerChainProposal{
				sampleProp1, sampleProp2, sampleProp3, sampleProp4,
			},
		},
		{
			propSubmitOrder: []types.StopConsumerChainProposal{
				sampleProp5, sampleProp4, sampleProp3, sampleProp2, sampleProp1,
			},
			accessTime: now.Add(5 * time.Hour),
			expectedOrderedProps: []types.StopConsumerChainProposal{
				sampleProp1, sampleProp2, sampleProp3, sampleProp4, sampleProp5,
			},
		},
	}

	for _, tc := range testCases {
		providerKeeper, ctx := testkeeper.GetProviderKeeperAndCtx(t)
		ctx = ctx.WithBlockTime(tc.accessTime)

		for _, prop := range tc.propSubmitOrder {
			providerKeeper.SetPendingStopProposal(ctx, prop.ChainId, prop.StopTime)
		}
		propsToExecute := providerKeeper.StopProposalsToExecute(ctx)
		require.Equal(t, tc.expectedOrderedProps, propsToExecute)
	}
}
