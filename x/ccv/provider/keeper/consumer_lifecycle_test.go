package keeper_test

import (
	"encoding/json"
	"fmt"
	"testing"
	"time"

	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
	ibctmtypes "github.com/cosmos/ibc-go/v8/modules/light-clients/07-tendermint"
	_go "github.com/cosmos/ics23/go"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"

	"cosmossdk.io/math"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	abci "github.com/cometbft/cometbft/abci/types"

	cryptotestutil "github.com/cosmos/interchain-security/v6/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/v6/testutil/keeper"
	providerkeeper "github.com/cosmos/interchain-security/v6/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/v6/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v6/x/ccv/types"
)

func TestPrepareConsumerForLaunch(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	spawnTime := time.Now().UTC()
	err := providerKeeper.PrepareConsumerForLaunch(ctx, CONSUMER_ID, time.Time{}, spawnTime)
	require.NoError(t, err)

	consumers, err := providerKeeper.GetConsumersToBeLaunched(ctx, spawnTime)
	require.NoError(t, err)
	require.Equal(t, providertypes.ConsumerIds{Ids: []string{CONSUMER_ID}}, consumers)

	nextSpawnTime := spawnTime.Add(time.Hour)
	err = providerKeeper.PrepareConsumerForLaunch(ctx, CONSUMER_ID, spawnTime, nextSpawnTime)
	require.NoError(t, err)

	consumers, err = providerKeeper.GetConsumersToBeLaunched(ctx, spawnTime)
	require.NoError(t, err)
	require.Empty(t, consumers)

	consumers, err = providerKeeper.GetConsumersToBeLaunched(ctx, nextSpawnTime)
	require.NoError(t, err)
	require.Equal(t, providertypes.ConsumerIds{Ids: []string{CONSUMER_ID}}, consumers)
}

func TestInitializeConsumer(t *testing.T) {
	now := time.Now().UTC()
	consumerId := "13"

	testCases := []struct {
		name           string
		spawnTime      time.Time
		setup          func(*providerkeeper.Keeper, sdk.Context, time.Time)
		expInitialized bool
	}{
		{
			name:      "valid",
			spawnTime: now,
			setup: func(pk *providerkeeper.Keeper, ctx sdk.Context, spawnTime time.Time) {
				pk.SetConsumerPhase(ctx, consumerId, providertypes.CONSUMER_PHASE_REGISTERED)
				err := pk.SetConsumerInitializationParameters(ctx, consumerId,
					providertypes.ConsumerInitializationParameters{
						SpawnTime: spawnTime,
					})
				require.NoError(t, err)
			},
			expInitialized: true,
		},
		{
			name:      "invalid: no phase",
			spawnTime: now,
			setup: func(pk *providerkeeper.Keeper, ctx sdk.Context, spawnTime time.Time) {
			},
			expInitialized: false,
		},
		{
			name:      "invalid: wrong phase",
			spawnTime: now,
			setup: func(pk *providerkeeper.Keeper, ctx sdk.Context, spawnTime time.Time) {
				pk.SetConsumerPhase(ctx, consumerId, providertypes.CONSUMER_PHASE_LAUNCHED)
				err := pk.SetConsumerInitializationParameters(ctx, consumerId,
					providertypes.ConsumerInitializationParameters{
						SpawnTime: spawnTime,
					})
				require.NoError(t, err)
			},
			expInitialized: false,
		},
		{
			name:      "invalid: no init params",
			spawnTime: now,
			setup: func(pk *providerkeeper.Keeper, ctx sdk.Context, spawnTime time.Time) {
				pk.SetConsumerPhase(ctx, consumerId, providertypes.CONSUMER_PHASE_REGISTERED)
			},
			expInitialized: false,
		},
		{
			name:      "invalid: zero spawn time",
			spawnTime: now,
			setup: func(pk *providerkeeper.Keeper, ctx sdk.Context, spawnTime time.Time) {
				pk.SetConsumerPhase(ctx, consumerId, providertypes.CONSUMER_PHASE_REGISTERED)
				err := pk.SetConsumerInitializationParameters(ctx, consumerId,
					providertypes.ConsumerInitializationParameters{
						SpawnTime: time.Time{},
					})
				require.NoError(t, err)
			},
			expInitialized: false,
		},
	}

	for _, tc := range testCases {
		pk, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
		defer ctrl.Finish()

		tc.setup(&pk, ctx, tc.spawnTime)

		spawnTime, initialized := pk.InitializeConsumer(ctx, consumerId)
		require.Equal(t, tc.expInitialized, initialized, tc.name)
		if initialized {
			require.Equal(t, tc.spawnTime, spawnTime, tc.name)
			require.Equal(t, providertypes.CONSUMER_PHASE_INITIALIZED, pk.GetConsumerPhase(ctx, consumerId))
		}
	}
}

// TestBeginBlockInit directly tests BeginBlockLaunchConsumers against the spec using helpers defined above.
func TestBeginBlockLaunchConsumers(t *testing.T) {
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
		},
	}

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
		err := providerKeeper.SetConsumerInitializationParameters(ctx, fmt.Sprintf("%d", i), r)
		require.NoError(t, err)
		// set up the chains in their initialized phase, hence they could launch
		providerKeeper.SetConsumerPhase(ctx, fmt.Sprintf("%d", i), providertypes.CONSUMER_PHASE_INITIALIZED)
		err = providerKeeper.AppendConsumerToBeLaunched(ctx, fmt.Sprintf("%d", i), r.SpawnTime)
		require.NoError(t, err)
	}
	for i, r := range powerShapingParameters {
		err := providerKeeper.SetConsumerPowerShapingParameters(ctx, fmt.Sprintf("%d", i), r)
		require.NoError(t, err)
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

	providerKeeper.BeginBlockLaunchConsumers(ctx)

	// first chain was successfully launched
	phase := providerKeeper.GetConsumerPhase(ctx, "0")
	require.Equal(t, providertypes.CONSUMER_PHASE_LAUNCHED, phase)
	_, found := providerKeeper.GetConsumerGenesis(ctx, "0")
	require.True(t, found)

	// second chain was successfully launched
	phase = providerKeeper.GetConsumerPhase(ctx, "1")
	require.Equal(t, providertypes.CONSUMER_PHASE_LAUNCHED, phase)
	_, found = providerKeeper.GetConsumerGenesis(ctx, "1")
	require.True(t, found)

	// third chain was not launched because its spawn time has not passed
	phase = providerKeeper.GetConsumerPhase(ctx, "2")
	require.Equal(t, providertypes.CONSUMER_PHASE_INITIALIZED, phase)
	_, found = providerKeeper.GetConsumerGenesis(ctx, "2")
	require.False(t, found)

	// fourth chain corresponds to an Opt-In chain with one opted-in validator and hence the chain gets
	// successfully executed
	phase = providerKeeper.GetConsumerPhase(ctx, "3")
	require.Equal(t, providertypes.CONSUMER_PHASE_LAUNCHED, phase)
	_, found = providerKeeper.GetConsumerGenesis(ctx, "3")
	require.True(t, found)

	// fifth chain corresponds to an Opt-In chain with no opted-in validators and hence the
	// chain launch is NOT successful
	phase = providerKeeper.GetConsumerPhase(ctx, "4")
	require.Equal(t, providertypes.CONSUMER_PHASE_INITIALIZED, phase)
	_, found = providerKeeper.GetConsumerGenesis(ctx, "4")
	require.False(t, found)
}

// TestGetConsumersReadyToLaunch tests that the ready to-be-launched consumer chains are returned
func TestGetConsumersReadyToLaunch(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// no chains to-be-launched exist
	require.Empty(t, providerKeeper.GetConsumersReadyToLaunch(ctx, 5))

	err := providerKeeper.AppendConsumerToBeLaunched(ctx, "consumerId1", time.Unix(10, 0))
	require.NoError(t, err)
	err = providerKeeper.AppendConsumerToBeLaunched(ctx, "consumerId2", time.Unix(20, 0))
	require.NoError(t, err)
	err = providerKeeper.AppendConsumerToBeLaunched(ctx, "consumerId3", time.Unix(30, 0))
	require.NoError(t, err)

	// time has not yet reached the spawn time of "consumerId1"
	ctx = ctx.WithBlockTime(time.Unix(9, 999999999))
	require.Empty(t, providerKeeper.GetConsumersReadyToLaunch(ctx, 3))

	// time has reached the spawn time of "consumerId1"
	ctx = ctx.WithBlockTime(time.Unix(10, 0))
	require.Equal(t, []string{"consumerId1"}, providerKeeper.GetConsumersReadyToLaunch(ctx, 3))

	// time has reached the spawn time of "consumerId1" and "consumerId2"
	ctx = ctx.WithBlockTime(time.Unix(20, 0))
	require.Equal(t, []string{"consumerId1", "consumerId2"}, providerKeeper.GetConsumersReadyToLaunch(ctx, 3))

	// time has reached the spawn time of all chains
	ctx = ctx.WithBlockTime(time.Unix(30, 0))
	require.Equal(t, []string{"consumerId1", "consumerId2", "consumerId3"}, providerKeeper.GetConsumersReadyToLaunch(ctx, 3))

	// limit the number of returned consumer chains
	require.Equal(t, []string{}, providerKeeper.GetConsumersReadyToLaunch(ctx, 0))
	require.Equal(t, []string{"consumerId1"}, providerKeeper.GetConsumersReadyToLaunch(ctx, 1))
	require.Equal(t, []string{"consumerId1", "consumerId2"}, providerKeeper.GetConsumersReadyToLaunch(ctx, 2))
}

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
				providerKeeper.SetConsumerPhase(ctx, "0", providertypes.CONSUMER_PHASE_INITIALIZED)

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
				providerKeeper.SetConsumerPhase(ctx, "0", providertypes.CONSUMER_PHASE_LAUNCHED)

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
		err := providerKeeper.SetConsumerMetadata(ctx, "0", testkeeper.GetTestConsumerMetadata())
		require.NoError(t, err)
		err = providerKeeper.SetConsumerInitializationParameters(ctx, "0", testkeeper.GetTestInitializationParameters())
		require.NoError(t, err)
		err = providerKeeper.SetConsumerPowerShapingParameters(ctx, "0", testkeeper.GetTestPowerShapingParameters())
		require.NoError(t, err)

		err = providerKeeper.CreateConsumerClient(ctx, "0")
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
	err := providerKeeper.SetConsumerMetadata(ctx, "0", consumerMetadata)
	require.NoError(t, err)
	err = providerKeeper.SetConsumerInitializationParameters(ctx, "0", initializationParameters)
	require.NoError(t, err)
	err = providerKeeper.SetConsumerPowerShapingParameters(ctx, "0", providertypes.PowerShapingParameters{})
	require.NoError(t, err)

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

func TestBeginBlockStopConsumers(t *testing.T) {
	now := time.Now().UTC()

	keeperParams := testkeeper.NewInMemKeeperParams(t)
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, keeperParams)
	providerKeeper.SetParams(ctx, providertypes.DefaultParams())
	defer ctrl.Finish()
	ctx = ctx.WithBlockTime(now)

	chainIds := []string{"chain1", "chain2", "chain3"}
	consumerIds := []string{"consumerId1", "consumerId2", "consumerId3"}
	err := providerKeeper.SetConsumerRemovalTime(ctx, consumerIds[0], now.Add(-time.Hour))
	require.NoError(t, err)
	err = providerKeeper.AppendConsumerToBeRemoved(ctx, consumerIds[0], now.Add(-time.Hour))
	require.NoError(t, err)
	err = providerKeeper.SetConsumerRemovalTime(ctx, consumerIds[1], now)
	require.NoError(t, err)
	err = providerKeeper.AppendConsumerToBeRemoved(ctx, consumerIds[1], now)
	require.NoError(t, err)
	err = providerKeeper.SetConsumerRemovalTime(ctx, consumerIds[2], now.Add(time.Hour))
	require.NoError(t, err)
	err = providerKeeper.AppendConsumerToBeRemoved(ctx, consumerIds[2], now.Add(time.Hour))
	require.NoError(t, err)

	//
	// Mock expectations
	//
	expectations := []*gomock.Call{}
	for i := range consumerIds {
		chainId := chainIds[i]
		// A consumer chain is setup corresponding to each consumerId, making these mocks necessary
		testkeeper.SetupMocksForLastBondedValidatorsExpectation(mocks.MockStakingKeeper, 0, []stakingtypes.Validator{}, 1)
		expectations = append(expectations, testkeeper.GetMocksForCreateConsumerClient(ctx, &mocks,
			chainId, clienttypes.NewHeight(2, 3))...)
		expectations = append(expectations, testkeeper.GetMocksForSetConsumerChain(ctx, &mocks, chainId)...)
	}
	// Only first two consumer chains should be stopped
	expectations = append(expectations, testkeeper.GetMocksForDeleteConsumerChain(ctx, &mocks)...)
	expectations = append(expectations, testkeeper.GetMocksForDeleteConsumerChain(ctx, &mocks)...)

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
		err = providerKeeper.SetConsumerMetadata(ctx, consumerId, registrationRecord)
		require.NoError(t, err)
		err = providerKeeper.SetConsumerInitializationParameters(ctx, consumerId, initializationRecord)
		require.NoError(t, err)
		err = providerKeeper.SetConsumerPowerShapingParameters(ctx, consumerId, testkeeper.GetTestPowerShapingParameters())
		require.NoError(t, err)
		providerKeeper.SetConsumerPhase(ctx, consumerId, providertypes.CONSUMER_PHASE_INITIALIZED)
		providerKeeper.SetConsumerClientId(ctx, consumerId, "clientID")

		err = providerKeeper.CreateConsumerClient(ctx, consumerId)
		require.NoError(t, err)
		err = providerKeeper.SetConsumerChain(ctx, "channelID")
		require.NoError(t, err)

		// the chain is considered to be stopped and ready for deletion (i.e., `StopAndPrepareForConsumerRemoval` is called)
		providerKeeper.SetConsumerPhase(ctx, consumerId, providertypes.CONSUMER_PHASE_STOPPED)
	}

	//
	// Test execution
	//

	providerKeeper.BeginBlockRemoveConsumers(ctx)

	// Only the 3rd (final) proposal is still stored as pending
	phase := providerKeeper.GetConsumerPhase(ctx, consumerIds[0])
	require.Equal(t, providertypes.CONSUMER_PHASE_DELETED, phase)
	phase = providerKeeper.GetConsumerPhase(ctx, consumerIds[1])
	require.Equal(t, providertypes.CONSUMER_PHASE_DELETED, phase)
	// third chain had a removal time in the future and hence did not get deleted
	phase = providerKeeper.GetConsumerPhase(ctx, consumerIds[2])
	require.Equal(t, providertypes.CONSUMER_PHASE_STOPPED, phase)
}

func TestGetConsumersReadyToStop(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// no chains to-be-stopped exist
	require.Empty(t, providerKeeper.GetConsumersReadyToStop(ctx, 3))

	err := providerKeeper.AppendConsumerToBeRemoved(ctx, "consumerId1", time.Unix(10, 0))
	require.NoError(t, err)
	err = providerKeeper.AppendConsumerToBeRemoved(ctx, "consumerId2", time.Unix(20, 0))
	require.NoError(t, err)
	err = providerKeeper.AppendConsumerToBeRemoved(ctx, "consumerId3", time.Unix(30, 0))
	require.NoError(t, err)

	// time has not yet reached the removal time of "consumerId1"
	ctx = ctx.WithBlockTime(time.Unix(9, 999999999))
	require.Empty(t, providerKeeper.GetConsumersReadyToStop(ctx, 3))

	// time has reached the removal time of "consumerId1"
	ctx = ctx.WithBlockTime(time.Unix(10, 0))
	require.Equal(t, []string{"consumerId1"}, providerKeeper.GetConsumersReadyToStop(ctx, 3))

	// time has reached the removal time of "consumerId1" and "consumerId2"
	ctx = ctx.WithBlockTime(time.Unix(20, 0))
	require.Equal(t, []string{"consumerId1", "consumerId2"}, providerKeeper.GetConsumersReadyToStop(ctx, 3))

	// time has reached the removal time of all chains
	ctx = ctx.WithBlockTime(time.Unix(30, 0))
	require.Equal(t, []string{"consumerId1", "consumerId2", "consumerId3"}, providerKeeper.GetConsumersReadyToStop(ctx, 3))
}

// Tests the DeleteConsumerChain method against the spec,
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
				testkeeper.SetupForDeleteConsumerChain(t, ctx, providerKeeper, mocks, consumerId)

				// set consumer minimum equivocation height
				providerKeeper.SetEquivocationEvidenceMinHeight(ctx, consumerId, 1)

				// assert mocks for expected calls to `DeleteConsumerChain` when closing the underlying channel
				gomock.InOrder(testkeeper.GetMocksForDeleteConsumerChain(ctx, &mocks)...)
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

		err := providerKeeper.DeleteConsumerChain(ctx, consumerId)

		if tc.expErr {
			require.Error(t, err, t)
		} else {
			require.NoError(t, err)
		}

		testkeeper.TestProviderStateIsCleanedAfterConsumerChainIsDeleted(t, ctx, providerKeeper, consumerId, "channelID", tc.expErr)

		ctrl.Finish()
	}
}

//
// Setters and Getters
//

// TestConsumerRemovalTime tests the getter, setter, and deletion of the consumer id to removal times methods
func TestConsumerRemovalTime(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	_, err := providerKeeper.GetConsumerRemovalTime(ctx, CONSUMER_ID)
	require.Error(t, err)

	expectedRemovalTime := time.Unix(1234, 56789)
	providerKeeper.SetConsumerRemovalTime(ctx, CONSUMER_ID, expectedRemovalTime)
	actualRemovalTime, err := providerKeeper.GetConsumerRemovalTime(ctx, CONSUMER_ID)
	require.NoError(t, err)
	require.Equal(t, actualRemovalTime, expectedRemovalTime)

	providerKeeper.DeleteConsumerRemovalTime(ctx, CONSUMER_ID)
	_, err = providerKeeper.GetConsumerRemovalTime(ctx, CONSUMER_ID)
	require.Error(t, err)
}

// TestConsumersToBeLaunched tests `AppendConsumerToBeLaunched`, `GetConsumersToBeLaunched`, and `RemoveConsumerToBeLaunched`
func TestConsumersToBeLaunched(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	spawnTime := time.Now()
	err := providerKeeper.AppendConsumerToBeLaunched(ctx, "consumerId1", spawnTime)
	require.NoError(t, err)
	consumers, err := providerKeeper.GetConsumersToBeLaunched(ctx, spawnTime)
	require.NoError(t, err)
	require.Equal(t, []string{"consumerId1"}, consumers.Ids)

	err = providerKeeper.AppendConsumerToBeLaunched(ctx, "consumerId2", spawnTime)
	require.NoError(t, err)
	consumers, err = providerKeeper.GetConsumersToBeLaunched(ctx, spawnTime)
	require.NoError(t, err)
	require.Equal(t, []string{"consumerId1", "consumerId2"}, consumers.Ids)

	err = providerKeeper.AppendConsumerToBeLaunched(ctx, "consumerId3", spawnTime)
	require.NoError(t, err)
	consumers, err = providerKeeper.GetConsumersToBeLaunched(ctx, spawnTime)
	require.NoError(t, err)
	require.Equal(t, []string{"consumerId1", "consumerId2", "consumerId3"}, consumers.Ids)

	err = providerKeeper.RemoveConsumerToBeLaunched(ctx, "consumerId2", spawnTime)
	require.NoError(t, err)
	consumers, err = providerKeeper.GetConsumersToBeLaunched(ctx, spawnTime)
	require.NoError(t, err)
	require.Equal(t, []string{"consumerId1", "consumerId3"}, consumers.Ids)

	// also add consumer ids under a different spawn time and verify everything under the original spawn time is still there
	spawnTimePlusOneHour := spawnTime.Add(time.Hour)
	err = providerKeeper.AppendConsumerToBeLaunched(ctx, "consumerId4", spawnTimePlusOneHour)
	require.NoError(t, err)
	consumers, err = providerKeeper.GetConsumersToBeLaunched(ctx, spawnTimePlusOneHour)
	require.NoError(t, err)
	require.Equal(t, []string{"consumerId4"}, consumers.Ids)

	consumers, err = providerKeeper.GetConsumersToBeLaunched(ctx, spawnTime)
	require.NoError(t, err)
	require.Equal(t, []string{"consumerId1", "consumerId3"}, consumers.Ids)

	// start removing all consumers from `spawnTime`
	err = providerKeeper.RemoveConsumerToBeLaunched(ctx, "consumerId3", spawnTime)
	require.NoError(t, err)
	err = providerKeeper.RemoveConsumerToBeLaunched(ctx, "consumerId1", spawnTime)
	require.NoError(t, err)
	consumers, err = providerKeeper.GetConsumersToBeLaunched(ctx, spawnTime)
	require.NoError(t, err)
	require.Empty(t, consumers.Ids)

	// remove from `spawnTimePlusOneHour`
	err = providerKeeper.RemoveConsumerToBeLaunched(ctx, "consumerId4", spawnTimePlusOneHour)
	require.NoError(t, err)
	consumers, err = providerKeeper.GetConsumersToBeLaunched(ctx, spawnTimePlusOneHour)
	require.NoError(t, err)
	require.Empty(t, consumers.Ids)

	// add another consumer for `spawnTime`
	err = providerKeeper.AppendConsumerToBeLaunched(ctx, "consumerId5", spawnTime)
	require.NoError(t, err)
	consumers, err = providerKeeper.GetConsumersToBeLaunched(ctx, spawnTime)
	require.NoError(t, err)
	require.Equal(t, []string{"consumerId5"}, consumers.Ids)
}

// TestConsumersToBeRemoved tests `AppendConsumerToBeRemoved`, `GetConsumersToBeRemoved`, and `RemoveConsumerToBeRemoved`
func TestConsumersToBeRemoved(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	removalTime := time.Now()
	err := providerKeeper.AppendConsumerToBeRemoved(ctx, "consumerId1", removalTime)
	require.NoError(t, err)
	consumers, err := providerKeeper.GetConsumersToBeRemoved(ctx, removalTime)
	require.NoError(t, err)
	require.Equal(t, []string{"consumerId1"}, consumers.Ids)

	err = providerKeeper.AppendConsumerToBeRemoved(ctx, "consumerId2", removalTime)
	require.NoError(t, err)
	consumers, err = providerKeeper.GetConsumersToBeRemoved(ctx, removalTime)
	require.NoError(t, err)
	require.Equal(t, []string{"consumerId1", "consumerId2"}, consumers.Ids)

	err = providerKeeper.AppendConsumerToBeRemoved(ctx, "consumerId3", removalTime)
	require.NoError(t, err)
	consumers, err = providerKeeper.GetConsumersToBeRemoved(ctx, removalTime)
	require.NoError(t, err)
	require.Equal(t, []string{"consumerId1", "consumerId2", "consumerId3"}, consumers.Ids)

	err = providerKeeper.RemoveConsumerToBeRemoved(ctx, "consumerId2", removalTime)
	require.NoError(t, err)
	consumers, err = providerKeeper.GetConsumersToBeRemoved(ctx, removalTime)
	require.NoError(t, err)
	require.Equal(t, []string{"consumerId1", "consumerId3"}, consumers.Ids)

	// also add consumer ids under a different removal time and verify everything under the original removal time is still there
	removalTimePlusOneHour := removalTime.Add(time.Hour)
	err = providerKeeper.AppendConsumerToBeRemoved(ctx, "consumerId4", removalTimePlusOneHour)
	require.NoError(t, err)
	consumers, err = providerKeeper.GetConsumersToBeRemoved(ctx, removalTimePlusOneHour)
	require.NoError(t, err)
	require.Equal(t, []string{"consumerId4"}, consumers.Ids)

	consumers, err = providerKeeper.GetConsumersToBeRemoved(ctx, removalTime)
	require.NoError(t, err)
	require.Equal(t, []string{"consumerId1", "consumerId3"}, consumers.Ids)

	// start removing all consumers from `removalTime`
	err = providerKeeper.RemoveConsumerToBeRemoved(ctx, "consumerId3", removalTime)
	require.NoError(t, err)
	err = providerKeeper.RemoveConsumerToBeRemoved(ctx, "consumerId1", removalTime)
	require.NoError(t, err)
	consumers, err = providerKeeper.GetConsumersToBeRemoved(ctx, removalTime)
	require.NoError(t, err)
	require.Empty(t, consumers.Ids)

	// remove from `removalTimePlusOneHour`
	err = providerKeeper.RemoveConsumerToBeRemoved(ctx, "consumerId4", removalTimePlusOneHour)
	require.NoError(t, err)
	consumers, err = providerKeeper.GetConsumersToBeRemoved(ctx, removalTimePlusOneHour)
	require.NoError(t, err)
	require.Empty(t, consumers.Ids)

	// add another consumer for `removalTime`
	err = providerKeeper.AppendConsumerToBeRemoved(ctx, "consumerId5", removalTime)
	require.NoError(t, err)
	consumers, err = providerKeeper.GetConsumersToBeRemoved(ctx, removalTime)
	require.NoError(t, err)
	require.Equal(t, []string{"consumerId5"}, consumers.Ids)
}
