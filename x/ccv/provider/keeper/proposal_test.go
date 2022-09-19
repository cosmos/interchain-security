package keeper_test

import (
	"testing"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	capabilitytypes "github.com/cosmos/cosmos-sdk/x/capability/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	conntypes "github.com/cosmos/ibc-go/v3/modules/core/03-connection/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
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

// Tests the HandleConsumerAdditionProposal method against the SpawnConsumerChainProposalHandler spec.
// See: https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/methods.md#ccv-pcf-spccprop1
// Spec tag: [CCV-PCF-SPCCPROP.1]
func TestHandleConsumerAdditionProposal(t *testing.T) {

	const (
		// Value to inject into mocked returned value for CreateClient in each test case
		clientIDToInject = "clientID"
	)

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
		ctrl := gomock.NewController(t)
		mocks := testkeeper.NewMockedKeepers(ctrl)
		ctx := keeperParams.Ctx
		providerKeeper := testkeeper.NewInMemProviderKeeper(keeperParams, mocks)

		ctx = ctx.WithBlockTime(tc.blockTime)

		if tc.expCreatedClient {
			// Mock calls are only asserted if we expect a client to be created.
			gomock.InOrder(
				getMocksForClientCreation(ctx, &mocks, "chainID", clienttypes.NewHeight(4, 5), "clientID")...,
			)

		}

		tc.prop.LockUnbondingOnTimeout = false // Full functionality not implemented yet.

		err := providerKeeper.HandleConsumerAdditionProposal(ctx, tc.prop)
		require.NoError(t, err)

		if tc.expCreatedClient {
			testCreatedConsumerClient(t, ctx, providerKeeper, tc.prop.ChainId, clientIDToInject)
		} else {
			// check that stored pending prop is exactly the same as the initially instantiated prop
			gotProposal := providerKeeper.GetPendingConsumerAdditionProp(ctx, tc.prop.SpawnTime, tc.prop.ChainId)
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
					getMocksForClientCreation(ctx, mocks, "chainID", clienttypes.NewHeight(4, 5), "clientID")...,
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
		ctrl := gomock.NewController(t)
		mocks := testkeeper.NewMockedKeepers(ctrl)
		ctx := keeperParams.Ctx
		providerKeeper := testkeeper.NewInMemProviderKeeper(keeperParams, mocks)

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

// Returns mock call expectations for a consumer client being created.
func getMocksForClientCreation(ctx sdk.Context, mocks *testkeeper.MockedKeepers,
	expectedChainID string, expectedLatestHeight clienttypes.Height, clientIDToInject string) []*gomock.Call {

	return []*gomock.Call{
		mocks.MockStakingKeeper.EXPECT().UnbondingTime(ctx).Return(time.Hour).Times(
			1, // called once in CreateConsumerClient
		),

		mocks.MockClientKeeper.EXPECT().CreateClient(
			ctx,
			// Allows us to expect a match by field. These are the only two client state values
			// that are dependant on parameters passed to CreateConsumerClient.
			extra.StructMatcher().Field(
				"ChainId", expectedChainID).Field(
				"LatestHeight", expectedLatestHeight,
			),
			gomock.Any(),
		).Return(clientIDToInject, nil).Times(1),

		mocks.MockStakingKeeper.EXPECT().UnbondingTime(ctx).Return(time.Hour).Times(
			1, // called again in MakeConsumerGenesis
		),

		mocks.MockClientKeeper.EXPECT().GetSelfConsensusState(ctx,
			clienttypes.GetSelfHeight(ctx)).Return(&ibctmtypes.ConsensusState{}, nil).Times(1),

		mocks.MockStakingKeeper.EXPECT().IterateLastValidatorPowers(ctx, gomock.Any()).Times(1),
	}
}

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
	providerKeeper, ctx, ctrl := testkeeper.GetProviderKeeperAndCtx(t)
	defer ctrl.Finish()

	for _, tc := range testCases {
		err := providerKeeper.SetPendingConsumerAdditionProp(ctx, &tc.ConsumerAdditionProposal)
		require.NoError(t, err)
	}

	ctx = ctx.WithBlockTime(time.Now().UTC())

	propsToExecute := providerKeeper.ConsumerAdditionPropsToExecute(ctx)
	// Delete consumer addition proposals, same as what would be done by IteratePendingConsumerAdditionProps
	providerKeeper.DeletePendingConsumerAdditionProps(ctx, propsToExecute...)
	numDeleted := 0
	for _, tc := range testCases {
		res := providerKeeper.GetPendingConsumerAdditionProp(ctx, tc.SpawnTime, tc.ChainId)
		if !tc.ExpDeleted {
			require.NotEmpty(t, res, "consumer addition proposal was deleted: %s %s", tc.ChainId, tc.SpawnTime.String())
			continue
		}
		require.Empty(t, res, "consumer addition proposal was not deleted %s %s", tc.ChainId, tc.SpawnTime.String())
		require.Equal(t, propsToExecute[numDeleted].ChainId, tc.ChainId)
		numDeleted += 1
	}
}

// Tests that pending consumer addition proposals are accessed in order by timestamp via the iterator
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
		providerKeeper, ctx, ctrl := testkeeper.GetProviderKeeperAndCtx(t)
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

func TestHandleConsumerRemovalProposal(t *testing.T) {

	type testCase struct {
		description string
		// Consumer removal proposal to handle
		prop *types.ConsumerRemovalProposal
		// State-mutating setup specific to this test case
		setup func(sdk.Context, *providerkeeper.Keeper)
		// Time when prop is handled
		blockTime time.Time
		// Whether we should expect the method to return an error
		expErr bool
		// Whether consumer chain should have been stopped
		expStop bool
	}

	// TODO: Make sure to cover everything that was covered before in the e2e test.

	// Snapshot times asserted in tests
	now := time.Now().UTC()
	hourFromNow := now.Add(time.Hour).UTC()

	tests := []testCase{
		{
			description: "valid stop consumer chain proposal: stop time reached",
			prop: providertypes.NewConsumerRemovalProposal(
				"title",
				"description",
				"chainId",
				now,
			).(*providertypes.ConsumerRemovalProposal),
			setup:     func(sdk.Context, *providerkeeper.Keeper) {},
			blockTime: hourFromNow, // After stop time.
			expErr:    false,
			expStop:   true,
		},
		// {
		// 	description: "valid proposal: stop time has not yet been reached",
		// 	prop: providertypes.NewConsumerRemovalProposal(
		// 		"title",
		// 		"description",
		// 		"chainId",
		// 		hourFromNow,
		// 	).(*providertypes.ConsumerRemovalProposal),
		// 	setup:     func(sdk.Context, *providerkeeper.Keeper) {},
		// 	blockTime: now, // Before proposal's stop time
		// 	expErr:    false,
		// 	expStop:   false,
		// },
		// {
		// 	description: "valid proposal: fail due to an invalid unbonding index",
		// 	prop: providertypes.NewConsumerRemovalProposal(
		// 		"title",
		// 		"description",
		// 		"chainId",
		// 		now,
		// 	).(*providertypes.ConsumerRemovalProposal),
		// 	setup: func(ctx sdk.Context, providerKeeper *providerkeeper.Keeper) {
		// 		// set invalid unbonding op index
		// 		providerKeeper.SetUnbondingOpIndex(ctx, "chainId", 0, []uint64{0})
		// 	},
		// 	blockTime: hourFromNow, // After stop time.
		// 	expErr:    true,
		// 	expStop:   true,
		// },
		// TODO: test case that client id already exists
	}

	for _, tc := range tests {
		// Common setup
		keeperParams := testkeeper.NewInMemKeeperParams(t)
		ctx := keeperParams.Ctx.WithBlockTime(tc.blockTime)
		testkeeper.SetTemplateClientState(ctx, keeperParams.ParamsSubspace)
		ctrl := gomock.NewController(t)
		mocks := testkeeper.NewMockedKeepers(ctrl)

		// Mock expectations
		injectedClientID := "clientID"
		expectations := getMocksForClientCreation(ctx, &mocks,
			tc.prop.ChainId, clienttypes.NewHeight(2, 3), injectedClientID)
		injectedChannelId := "channelID"

		// Mocks for SetConsumerChain called below
		expectations = append(expectations,
			mocks.MockChannelKeeper.EXPECT().GetChannel(ctx, ccv.ProviderPortID, gomock.Any()).Return(
				channeltypes.Channel{
					State:          channeltypes.OPEN,
					ConnectionHops: []string{"connectionID"},
				},
				true,
			).Times(1),
			mocks.MockConnectionKeeper.EXPECT().GetConnection(ctx, "connectionID").Return(
				conntypes.ConnectionEnd{ClientId: injectedClientID}, true,
			).Times(1),
			mocks.MockClientKeeper.EXPECT().GetClientState(ctx, injectedClientID).Return(
				&ibctmtypes.ClientState{ChainId: tc.prop.ChainId}, true,
			).Times(1),
		)

		// Mocks for actually stopping the consumer chain
		expectations = append(expectations,
			getMocksForStoppingConsumer(ctx, &mocks, injectedChannelId)...,
		)
		gomock.InOrder(expectations...)

		// Keeper setup
		providerKeeper := testkeeper.NewInMemProviderKeeper(keeperParams, mocks)
		err := providerKeeper.CreateConsumerClient(ctx, tc.prop.ChainId, clienttypes.NewHeight(2, 3), false)
		require.NoError(t, err)
		err = providerKeeper.SetConsumerChain(ctx, injectedChannelId)
		require.NoError(t, err)

		// Setup specific to test case
		tc.setup(ctx, &providerKeeper)

		err = providerKeeper.HandleConsumerRemovalProposal(ctx, tc.prop)

		if tc.expErr {
			require.Error(t, err)
		} else {
			require.NoError(t, err)
		}

		if tc.expStop {
			testStoppedConsumerChain(t, ctx, providerKeeper, tc.prop.ChainId, injectedChannelId)
		} else {
			// Proposal should be stored as pending
			found := providerKeeper.GetPendingConsumerRemovalProp(ctx, tc.prop.ChainId, tc.prop.StopTime)
			require.True(t, found)
			// double check that a client for this chain does still exist
			_, found = providerKeeper.GetConsumerClientId(ctx, tc.prop.ChainId)
			require.True(t, found)
		}

		// Assert mock calls from setup functions
		ctrl.Finish()
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

// Returns mock call expectations for a consumer being stopped. See StopConsumerChain
func getMocksForStoppingConsumer(ctx sdk.Context, mocks *testkeeper.MockedKeepers,
	channelIDToInject string) []*gomock.Call {
	dummyCap := &capabilitytypes.Capability{}
	return []*gomock.Call{
		// mocks.MockScopedKeeper.EXPECT().GetCapability(ctx, gomock.Any()).Return(dummyCap, true).Times(1),
		mocks.MockChannelKeeper.EXPECT().GetChannel(ctx, ccv.ProviderPortID, channelIDToInject).Return(
			channeltypes.Channel{State: channeltypes.OPEN}, true,
		).Times(1),
		mocks.MockScopedKeeper.EXPECT().GetCapability(ctx, gomock.Any()).Return(dummyCap, true).Times(1),
		mocks.MockChannelKeeper.EXPECT().ChanCloseInit(ctx, ccv.ProviderPortID, channelIDToInject, dummyCap).Times(1),
	}
}

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
	providerKeeper, ctx, ctrl := testkeeper.GetProviderKeeperAndCtx(t)
	defer ctrl.Finish()

	for _, tc := range testCases {
		providerKeeper.SetPendingConsumerRemovalProp(ctx, tc.ChainId, tc.StopTime)
	}

	ctx = ctx.WithBlockTime(time.Now().UTC())

	propsToExecute := providerKeeper.ConsumerRemovalPropsToExecute(ctx)
	// Delete consumer removal proposals, same as what would be done by IteratePendingConsumerRemovalProps
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
		providerKeeper, ctx, ctrl := testkeeper.GetProviderKeeperAndCtx(t)
		defer ctrl.Finish()
		ctx = ctx.WithBlockTime(tc.accessTime)

		for _, prop := range tc.propSubmitOrder {
			providerKeeper.SetPendingConsumerRemovalProp(ctx, prop.ChainId, prop.StopTime)
		}
		propsToExecute := providerKeeper.ConsumerRemovalPropsToExecute(ctx)
		require.Equal(t, tc.expectedOrderedProps, propsToExecute)
	}
}
