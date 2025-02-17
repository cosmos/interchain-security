package keeper_test

import (
	"encoding/json"
	"fmt"
	"testing"
	"time"

	clienttypes "github.com/cosmos/ibc-go/v10/modules/core/02-client/types"
	ibctmtypes "github.com/cosmos/ibc-go/v10/modules/light-clients/07-tendermint"
	ibctesting "github.com/cosmos/ibc-go/v10/testing"
	_go "github.com/cosmos/ics23/go"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"

	"cosmossdk.io/math"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	abci "github.com/cometbft/cometbft/abci/types"
	tmprotocrypto "github.com/cometbft/cometbft/proto/tendermint/crypto"

	cryptotestutil "github.com/cosmos/interchain-security/v7/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/v7/testutil/keeper"
	providerkeeper "github.com/cosmos/interchain-security/v7/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/v7/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v7/x/ccv/types"
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
	consumerId := CONSUMER_ID
	chainId := CONSUMER_CHAIN_ID

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
				pk.SetConsumerChainId(ctx, consumerId, chainId)
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
				pk.SetConsumerChainId(ctx, consumerId, chainId)
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
				pk.SetConsumerChainId(ctx, consumerId, chainId)
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
	chainIds := []string{"chain0", "chain1", "chain2", "chain3", "chain4"}

	initializationParameters := []providertypes.ConsumerInitializationParameters{
		{
			InitialHeight:                     clienttypes.NewHeight(0, 4),
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
			InitialHeight:                     clienttypes.NewHeight(0, 4),
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
			InitialHeight:                     clienttypes.NewHeight(0, 4),
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
			InitialHeight:                     clienttypes.NewHeight(0, 4),
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
			InitialHeight:                     clienttypes.NewHeight(0, 4),
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
			Prioritylist:       []string{},
		},
		{
			Top_N:              50,
			ValidatorsPowerCap: 0,
			ValidatorSetCap:    0,
			Allowlist:          []string{},
			Denylist:           []string{},
			Prioritylist:       []string{},
		},
		{
			Top_N:              50,
			ValidatorsPowerCap: 0,
			ValidatorSetCap:    0,
			Allowlist:          []string{},
			Denylist:           []string{},
			Prioritylist:       []string{},
		},
		{
			Top_N:              0,
			ValidatorsPowerCap: 0,
			ValidatorSetCap:    0,
			Allowlist:          []string{},
			Denylist:           []string{},
			Prioritylist:       []string{},
		},
		{
			Top_N:              0,
			ValidatorsPowerCap: 0,
			ValidatorSetCap:    0,
			Allowlist:          []string{},
			Denylist:           []string{},
			Prioritylist:       []string{},
		},
	}

	// set up all the records
	for i, chainId := range chainIds {
		providerKeeper.SetConsumerChainId(ctx, fmt.Sprintf("%d", i), chainId)
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

	providerKeeper.SetOptedIn(ctx, "3", providertypes.NewProviderConsAddress(consAddr))

	// Expect genesis and client creation for only the first, second, and fifth chains (spawn time already passed and valid)
	expectedCalls := testkeeper.GetMocksForMakeConsumerGenesis(ctx, &mocks, time.Hour)
	expectedCalls = append(expectedCalls, testkeeper.GetMocksForCreateConsumerClient(ctx, &mocks, "chain0", clienttypes.NewHeight(0, 4))...)
	expectedCalls = append(expectedCalls, testkeeper.GetMocksForMakeConsumerGenesis(ctx, &mocks, time.Hour)...)
	expectedCalls = append(expectedCalls, testkeeper.GetMocksForCreateConsumerClient(ctx, &mocks, "chain1", clienttypes.NewHeight(0, 4))...)
	expectedCalls = append(expectedCalls, testkeeper.GetMocksForMakeConsumerGenesis(ctx, &mocks, time.Hour)...)
	expectedCalls = append(expectedCalls, testkeeper.GetMocksForCreateConsumerClient(ctx, &mocks, "chain3", clienttypes.NewHeight(0, 4))...)

	gomock.InOrder(expectedCalls...)

	err := providerKeeper.BeginBlockLaunchConsumers(ctx)
	require.NoError(t, err)

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
	require.Equal(t, providertypes.CONSUMER_PHASE_REGISTERED, phase)
	_, found = providerKeeper.GetConsumerGenesis(ctx, "4")
	require.False(t, found)
}

func TestConsumeIdsFromTimeQueue(t *testing.T) {
	expectedConsumerIds := []string{"1", "2", "3", "4"}
	timestamps := []time.Time{time.Unix(10, 0), time.Unix(20, 0), time.Unix(30, 0)}

	testCases := []struct {
		name       string
		ts         time.Time
		limit      int
		expOutcome func(sdk.Context, []string, func(sdk.Context, time.Time) (providertypes.ConsumerIds, error))
	}{
		{
			name:  "timestamp too early",
			ts:    time.Unix(9, 999999999),
			limit: 3,
			expOutcome: func(ctx sdk.Context, ids []string, getIds func(sdk.Context, time.Time) (providertypes.ConsumerIds, error)) {
				require.Empty(t, ids)
			},
		},
		{
			name:  "first timestamp",
			ts:    timestamps[0],
			limit: 2,
			expOutcome: func(ctx sdk.Context, ids []string, getIds func(sdk.Context, time.Time) (providertypes.ConsumerIds, error)) {
				require.Equal(t, expectedConsumerIds[0:2], ids)

				// check that all consumers where removed
				consumerIds, err := getIds(ctx, timestamps[0])
				require.NoError(t, err)
				require.Empty(t, consumerIds)
			},
		},
		{
			name:  "first timestamp, with limit",
			ts:    timestamps[0],
			limit: 1,
			expOutcome: func(ctx sdk.Context, ids []string, getIds func(sdk.Context, time.Time) (providertypes.ConsumerIds, error)) {
				require.Equal(t, expectedConsumerIds[0:1], ids)

				// second consumer remained
				ret, err := getIds(ctx, timestamps[0])
				require.NoError(t, err)
				require.Equal(t, providertypes.ConsumerIds{
					Ids: []string{expectedConsumerIds[1]},
				}, ret)
			},
		},
		{
			name:  "second timestamp",
			ts:    timestamps[1],
			limit: 3,
			expOutcome: func(ctx sdk.Context, ids []string, getIds func(sdk.Context, time.Time) (providertypes.ConsumerIds, error)) {
				require.Equal(t, expectedConsumerIds[0:3], ids)

				// check that all consumers where removed
				ret, err := getIds(ctx, timestamps[0])
				require.NoError(t, err)
				require.Empty(t, ret)
				ret, err = getIds(ctx, timestamps[1])
				require.NoError(t, err)
				require.Empty(t, ret)
			},
		},
		{
			name:  "third timestamp, with limit",
			ts:    timestamps[1],
			limit: 3,
			expOutcome: func(ctx sdk.Context, ids []string, getIds func(sdk.Context, time.Time) (providertypes.ConsumerIds, error)) {
				require.Equal(t, expectedConsumerIds[0:3], ids)

				// 4th consumer remained
				ret, err := getIds(ctx, timestamps[0])
				require.NoError(t, err)
				require.Empty(t, ret)
				ret, err = getIds(ctx, timestamps[1])
				require.NoError(t, err)
				require.Empty(t, ret)
				ret, err = getIds(ctx, timestamps[2])
				require.NoError(t, err)
				require.Equal(t, providertypes.ConsumerIds{
					Ids: []string{expectedConsumerIds[3]},
				}, ret)
			},
		},
	}

	// test for consumers to be launched
	for _, tc := range testCases {
		providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
		defer ctrl.Finish()

		callCases := []struct {
			timeQueueKeyPrefix byte
			getIds             func(sdk.Context, time.Time) (providertypes.ConsumerIds, error)
			deleteAllIds       func(sdk.Context, time.Time)
			appendId           func(sdk.Context, string, time.Time) error
		}{
			{
				timeQueueKeyPrefix: providertypes.SpawnTimeToConsumerIdsKeyPrefix(),
				getIds:             providerKeeper.GetConsumersToBeLaunched,
				deleteAllIds:       providerKeeper.DeleteAllConsumersToBeLaunched,
				appendId:           providerKeeper.AppendConsumerToBeLaunched,
			},
			{
				timeQueueKeyPrefix: providertypes.RemovalTimeToConsumerIdsKeyPrefix(),
				getIds:             providerKeeper.GetConsumersToBeRemoved,
				deleteAllIds:       providerKeeper.DeleteAllConsumersToBeRemoved,
				appendId:           providerKeeper.AppendConsumerToBeRemoved,
			},
		}
		for _, cc := range callCases {
			err := cc.appendId(ctx, expectedConsumerIds[0], timestamps[0])
			require.NoError(t, err)
			err = cc.appendId(ctx, expectedConsumerIds[1], timestamps[0])
			require.NoError(t, err)
			err = cc.appendId(ctx, expectedConsumerIds[2], timestamps[1])
			require.NoError(t, err)
			err = cc.appendId(ctx, expectedConsumerIds[3], timestamps[2])
			require.NoError(t, err)

			ctx = ctx.WithBlockTime(tc.ts)

			consumerIds, err := providerKeeper.ConsumeIdsFromTimeQueue(
				ctx,
				cc.timeQueueKeyPrefix,
				cc.getIds,
				cc.deleteAllIds,
				cc.appendId,
				tc.limit,
			)
			require.NoError(t, err)

			tc.expOutcome(ctx, consumerIds, cc.getIds)
		}
	}
}

func TestHasActiveValidatorOptedIn(t *testing.T) {
	keeperParams := testkeeper.NewInMemKeeperParams(t)
	providerKeeper, ctx, _, mocks := testkeeper.GetProviderKeeperAndCtx(t, keeperParams)

	// set 5 bonded validators with powers 5, 4, 3, 2, and 1
	NumberOfBondedValidators := 5
	var bondedValidators []stakingtypes.Validator
	for i := 0; i < NumberOfBondedValidators; i++ {
		power := int64(NumberOfBondedValidators - i)
		bondedValidators = append(bondedValidators, createStakingValidator(ctx, mocks, power, i))
	}
	mocks.MockStakingKeeper.EXPECT().GetBondedValidatorsByPower(gomock.Any()).Return(bondedValidators, nil).AnyTimes()

	// get the consensus addresses of the previously-set bonded validators
	var consensusAddresses [][]byte
	for i := 0; i < NumberOfBondedValidators; i++ {
		consAddr, _ := bondedValidators[i].GetConsAddr()
		consensusAddresses = append(consensusAddresses, consAddr)
	}

	// Set the maximum number of provider consensus active validators (i.e., active validators) to 3. As a result
	// `bondedValidators[0]` (with power of 5), `bondedValidators[1]` (with power of 4), `bondedValidators[2]` (with power of 3)
	// are the active validators, and `bondedValidators[3]` (with power of 2) and `bondedValidators[4]` (with power of 1)
	// are non-active validators.
	maxProviderConsensusValidators := int64(3)
	params := providerKeeper.GetParams(ctx)
	params.MaxProviderConsensusValidators = maxProviderConsensusValidators
	providerKeeper.SetParams(ctx, params)

	activeValidators, _ := providerKeeper.GetLastProviderConsensusActiveValidators(ctx)

	consumerId := "0"

	// consumer chain has only non-active validators
	err := providerKeeper.SetConsumerValSet(ctx, consumerId, []providertypes.ConsensusValidator{
		{ProviderConsAddr: consensusAddresses[3]},
		{ProviderConsAddr: consensusAddresses[4]},
	})
	require.NoError(t, err)
	hasActiveValidatorOptedIn, err := providerKeeper.HasActiveConsumerValidator(ctx, consumerId, activeValidators)
	require.NoError(t, err)
	require.False(t, hasActiveValidatorOptedIn)

	// consumer chain has one active validator
	err = providerKeeper.SetConsumerValSet(ctx, consumerId, []providertypes.ConsensusValidator{
		{ProviderConsAddr: consensusAddresses[2]},
	})
	require.NoError(t, err)
	hasActiveValidatorOptedIn, err = providerKeeper.HasActiveConsumerValidator(ctx, consumerId, activeValidators)
	require.NoError(t, err)
	require.True(t, hasActiveValidatorOptedIn)

	// consumer chain has one active and two non-active validators
	err = providerKeeper.SetConsumerValSet(ctx, consumerId, []providertypes.ConsensusValidator{
		{ProviderConsAddr: consensusAddresses[3]},
		{ProviderConsAddr: consensusAddresses[4]},
		{ProviderConsAddr: consensusAddresses[1]},
	})
	require.NoError(t, err)
	hasActiveValidatorOptedIn, err = providerKeeper.HasActiveConsumerValidator(ctx, consumerId, activeValidators)
	require.NoError(t, err)
	require.True(t, hasActiveValidatorOptedIn)
}

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
				providerKeeper.SetConsumerPhase(ctx, CONSUMER_ID, providertypes.CONSUMER_PHASE_INITIALIZED)

				// Valid client creation is asserted with mock expectations here
				gomock.InOrder(
					testkeeper.GetMocksForCreateConsumerClient(ctx, mocks, CONSUMER_CHAIN_ID, clienttypes.NewHeight(0, 5))...,
				)
			},
			expClientCreated: true,
		},
		{
			description: "chain for this consumer id has already launched, and hence client was created, NO new one is created",
			setup: func(providerKeeper *providerkeeper.Keeper, ctx sdk.Context, mocks *testkeeper.MockedKeepers) {
				providerKeeper.SetConsumerPhase(ctx, CONSUMER_ID, providertypes.CONSUMER_PHASE_LAUNCHED)

				// Expect none of the client creation related calls to happen
				mocks.MockClientKeeper.EXPECT().CreateClient(gomock.Any(), gomock.Any(), gomock.Any(),
					gomock.Any()).Times(0)
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
		providerKeeper.SetConsumerChainId(ctx, CONSUMER_ID, CONSUMER_CHAIN_ID)
		err := providerKeeper.SetConsumerInitializationParameters(ctx, CONSUMER_ID, testkeeper.GetTestInitializationParameters())
		require.NoError(t, err)

		err = providerKeeper.CreateConsumerClient(ctx, CONSUMER_ID, []byte{})
		if tc.expClientCreated {
			require.NoError(t, err)
			clientId, found := providerKeeper.GetConsumerClientId(ctx, CONSUMER_ID)
			require.True(t, found)
			require.Equal(t, "clientID", clientId)
		} else {
			require.Error(t, err)
		}

		// Assert mock calls from setup functions
		ctrl.Finish()
	}
}

// TestMakeConsumerGenesis tests the MakeConsumerGenesis keeper method.
// An expected genesis state is hardcoded in json, unmarshaled, and compared
// against an actual consumer genesis state constructed by a provider keeper.
func TestMakeConsumerGenesis(t *testing.T) {
	keeperParams := testkeeper.NewInMemKeeperParams(t)
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, keeperParams)
	defer ctrl.Finish()

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

	// matches params from jsonString
	ccvTimeoutPeriod := time.Duration(2419200000000000)
	transferTimeoutPeriod := time.Duration(3600000000000)
	consumerUnbondingPeriod := time.Duration(1728000000000000)
	providerUnbondingPeriod := time.Duration(1814400000000000)
	trustingPeriod := time.Duration(1197504000000000)
	providerChainId := "provider-1"
	providerRevisionNumber := uint64(1)
	providerRevisionHeight := int64(5)

	initializationParameters := providertypes.ConsumerInitializationParameters{
		BlocksPerDistributionTransmission: 1000,
		CcvTimeoutPeriod:                  ccvTimeoutPeriod,
		TransferTimeoutPeriod:             transferTimeoutPeriod,
		ConsumerRedistributionFraction:    "0.75",
		HistoricalEntries:                 10000,
		UnbondingPeriod:                   consumerUnbondingPeriod,
	}

	//
	// Other setup not covered by custom template client state
	//
	ctx = ctx.WithChainID(providerChainId)            // consumerId is obtained from ctx
	ctx = ctx.WithBlockHeight(providerRevisionHeight) // RevisionHeight obtained from ctx
	gomock.InOrder(testkeeper.GetMocksForMakeConsumerGenesis(ctx, &mocks, providerUnbondingPeriod)...)

	providerKeeper.SetConsumerChainId(ctx, CONSUMER_ID, CONSUMER_CHAIN_ID)
	err := providerKeeper.SetConsumerInitializationParameters(ctx, CONSUMER_ID, initializationParameters)
	require.NoError(t, err)

	_, pks, _ := ibctesting.GenerateKeys(t, 2)
	var ppks [2]tmprotocrypto.PublicKey
	for i, pk := range pks {
		ppks[i], _ = cryptocodec.ToCmtProtoPublicKey(pk)
	}
	initialValUpdates := []abci.ValidatorUpdate{
		{PubKey: ppks[0], Power: 1},
		{PubKey: ppks[1], Power: 2},
	}

	actualGenesis, err := providerKeeper.MakeConsumerGenesis(ctx, CONSUMER_ID, initialValUpdates)
	require.NoError(t, err)

	// JSON string with tabs, newlines and spaces for readability
	jsonString := fmt.Sprintf(`{
		"params": {
			"enabled": true,
			"blocks_per_distribution_transmission": %d,
			"ccv_timeout_period": %d,
			"transfer_timeout_period": %d,
			"consumer_redistribution_fraction": "%s",
			"historical_entries": %d,
			"unbonding_period": %d,
			"soft_opt_out_threshold": "0",
			"reward_denoms": [],
			"provider_reward_denoms": [],
			"retry_delay_period": %d,
			"consumer_id": "%s"
		},
		"new_chain": true,
		"provider" : {
			"client_state": {
				"chain_id": "%s",
				"trust_level": {
					"numerator": 1,
					"denominator": 3
				},
				"trusting_period": %d,
				"unbonding_period": %d,
				"max_clock_drift": %d,
				"frozen_height": {},
				"latest_height": {
					"revision_number": %d,
					"revision_height": %d
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
			"initial_val_set": [{}]
		}
	}`,
		initializationParameters.BlocksPerDistributionTransmission,
		ccvTimeoutPeriod.Nanoseconds(),
		transferTimeoutPeriod.Nanoseconds(),
		initializationParameters.ConsumerRedistributionFraction,
		initializationParameters.HistoricalEntries,
		consumerUnbondingPeriod.Nanoseconds(),
		ccvtypes.DefaultRetryDelayPeriod.Nanoseconds(),
		CONSUMER_ID,
		providerChainId,
		trustingPeriod.Nanoseconds(),
		providerUnbondingPeriod.Nanoseconds(),
		providertypes.DefaultMaxClockDrift.Nanoseconds(),
		providerRevisionNumber,
		providerRevisionHeight,
	)

	var expectedGenesis ccvtypes.ConsumerGenesisState
	err = json.Unmarshal([]byte(jsonString), &expectedGenesis) // ignores tabs, newlines and spaces
	require.NoError(t, err)
	expectedGenesis.Provider.InitialValSet = initialValUpdates

	// Zeroing out different fields that are challenging to mock
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
		expectations = append(expectations, testkeeper.GetMocksForCreateConsumerClient(ctx, &mocks,
			chainId, clienttypes.NewHeight(0, 3))...)
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
		initializationRecord.InitialHeight = clienttypes.NewHeight(0, 3)
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

		err = providerKeeper.CreateConsumerClient(ctx, consumerId, []byte{})
		require.NoError(t, err)
		err = providerKeeper.SetConsumerChain(ctx, "channelID")
		require.NoError(t, err)

		// the chain is considered to be stopped and ready for deletion (i.e., `StopAndPrepareForConsumerRemoval` is called)
		providerKeeper.SetConsumerPhase(ctx, consumerId, providertypes.CONSUMER_PHASE_STOPPED)
	}

	//
	// Test execution
	//

	err = providerKeeper.BeginBlockRemoveConsumers(ctx)
	require.NoError(t, err)

	// Only the 3rd (final) proposal is still stored as pending
	phase := providerKeeper.GetConsumerPhase(ctx, consumerIds[0])
	require.Equal(t, providertypes.CONSUMER_PHASE_DELETED, phase)
	phase = providerKeeper.GetConsumerPhase(ctx, consumerIds[1])
	require.Equal(t, providertypes.CONSUMER_PHASE_DELETED, phase)
	// third chain had a removal time in the future and hence did not get deleted
	phase = providerKeeper.GetConsumerPhase(ctx, consumerIds[2])
	require.Equal(t, providertypes.CONSUMER_PHASE_STOPPED, phase)
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
