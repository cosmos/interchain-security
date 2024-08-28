package keeper_test

import (
	"testing"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	govv1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	"github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
	testkeeper "github.com/cosmos/interchain-security/v5/testutil/keeper"
	"github.com/cosmos/interchain-security/v5/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"
)

// TestConsumerId tests setters and getters of consumer id (i.e., `FetchAndIncrementConsumerId` and `GetConsumerId`)
func TestConsumerId(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	_, found := providerKeeper.GetConsumerId(ctx)
	require.False(t, found)

	consumerId := providerKeeper.FetchAndIncrementConsumerId(ctx)
	require.Equal(t, "0", consumerId)
	consumerIdNum, found := providerKeeper.GetConsumerId(ctx)
	require.Equal(t, uint64(1), consumerIdNum)
	require.True(t, found)

	consumerId = providerKeeper.FetchAndIncrementConsumerId(ctx)
	require.Equal(t, "1", consumerId)
	consumerIdNum, found = providerKeeper.GetConsumerId(ctx)
	require.Equal(t, uint64(2), consumerIdNum)
	require.True(t, found)
}

// TestConsumerChainId tests the getter, setter, and deletion of the consumer to chain id methods
func TestConsumerChainId(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	_, err := providerKeeper.GetConsumerChainId(ctx, "chainId")
	require.Error(t, err, "failed to retrieve chain id")

	providerKeeper.SetConsumerChainId(ctx, "chainId", "chainId")
	chainId, err := providerKeeper.GetConsumerChainId(ctx, "chainId")
	require.NoError(t, err)
	require.Equal(t, "chainId", chainId)

	// write under a different key
	providerKeeper.SetConsumerChainId(ctx, "consumerId2", "chainId")
	chainId, err = providerKeeper.GetConsumerChainId(ctx, "consumerId2")
	require.NoError(t, err)
	require.Equal(t, "chainId", chainId)

	// assert that overwriting the current key works
	providerKeeper.SetConsumerChainId(ctx, "chainId", "chainId2")
	chainId, err = providerKeeper.GetConsumerChainId(ctx, "chainId")
	require.NoError(t, err)
	require.Equal(t, "chainId2", chainId)

	providerKeeper.DeleteConsumerChainId(ctx, "chainId")
	_, err = providerKeeper.GetConsumerChainId(ctx, "chainId")
	require.Error(t, err, "failed to retrieve chain id")
}

// TestConsumerOwnerAddress tests the getter, setter, and deletion of the consumer to owner address methods
func TestConsumerOwnerAddress(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	_, err := providerKeeper.GetConsumerOwnerAddress(ctx, "ownerAddress")
	require.Error(t, err, "failed to retrieve owner address")

	providerKeeper.SetConsumerOwnerAddress(ctx, "consumerId", "owner address")
	ownerAddress, err := providerKeeper.GetConsumerOwnerAddress(ctx, "consumerId")
	require.NoError(t, err)
	require.Equal(t, "owner address", ownerAddress)

	// write under a different key
	providerKeeper.SetConsumerOwnerAddress(ctx, "consumerId2", "owner address")
	ownerAddress, err = providerKeeper.GetConsumerOwnerAddress(ctx, "consumerId2")
	require.NoError(t, err)
	require.Equal(t, "owner address", ownerAddress)

	// assert that overwriting the current key works
	providerKeeper.SetConsumerOwnerAddress(ctx, "consumerId", "owner address2")
	ownerAddress, err = providerKeeper.GetConsumerOwnerAddress(ctx, "consumerId")
	require.NoError(t, err)
	require.Equal(t, "owner address2", ownerAddress)

	providerKeeper.DeleteConsumerOwnerAddress(ctx, "consumerId")
	_, err = providerKeeper.GetConsumerChainId(ctx, "consumerId")
	require.Error(t, err, "failed to retrieve owner address")
}

// TestConsumerMetadata tests the getter, setter, and deletion of the consumer id to consumer metadata methods
func TestConsumerMetadata(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	_, err := providerKeeper.GetConsumerMetadata(ctx, "consumerId")
	require.Error(t, err)

	expectedMetadata := providertypes.ConsumerMetadata{
		Name:        "name",
		Description: "description",
		Metadata:    "metadata",
		//ChainId:     "chain_id",
	}
	providerKeeper.SetConsumerMetadata(ctx, "consumerId", expectedMetadata)
	actualMetadata, err := providerKeeper.GetConsumerMetadata(ctx, "consumerId")
	require.NoError(t, err)
	require.Equal(t, expectedMetadata, actualMetadata)

	// assert that overwriting the current registration record works
	expectedMetadata = providertypes.ConsumerMetadata{
		Name:        "name 2",
		Description: "description 2",
		Metadata:    "metadata 2",
		//ChainId:     "chain_id2",
	}
	providerKeeper.SetConsumerMetadata(ctx, "consumerId", expectedMetadata)
	actualMetadata, err = providerKeeper.GetConsumerMetadata(ctx, "consumerId")
	require.NoError(t, err)
	require.Equal(t, expectedMetadata, actualMetadata)

	providerKeeper.DeleteConsumerMetadata(ctx, "consumerId")
	actualMetadata, err = providerKeeper.GetConsumerMetadata(ctx, "consumerId")
	require.Error(t, err)
	require.Equal(t, providertypes.ConsumerMetadata{}, actualMetadata)
}

// TestConsumerInitializationParameters tests the getter, setter, and deletion of the consumer id to initialization parameters methods
func TestConsumerInitializationParameters(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	_, err := providerKeeper.GetConsumerInitializationParameters(ctx, "consumerId")
	require.Error(t, err)

	expectedInitializationParameters := providertypes.ConsumerInitializationParameters{
		InitialHeight:                     types.Height{RevisionNumber: 1, RevisionHeight: 2},
		GenesisHash:                       []byte{0, 1},
		BinaryHash:                        []byte{2, 3},
		SpawnTime:                         time.Unix(1, 2).UTC(),
		UnbondingPeriod:                   time.Duration(3456),
		CcvTimeoutPeriod:                  time.Duration(789),
		TransferTimeoutPeriod:             time.Duration(101112),
		ConsumerRedistributionFraction:    "consumer_redistribution_fraction",
		BlocksPerDistributionTransmission: 123,
		HistoricalEntries:                 456,
		DistributionTransmissionChannel:   "distribution_transmission_channel",
	}
	providerKeeper.SetConsumerInitializationParameters(ctx, "consumerId", expectedInitializationParameters)
	actualInitializationParameters, err := providerKeeper.GetConsumerInitializationParameters(ctx, "consumerId")
	require.NoError(t, err)
	require.Equal(t, expectedInitializationParameters, actualInitializationParameters)

	// assert that overwriting the current initialization record works
	expectedInitializationParameters = providertypes.ConsumerInitializationParameters{
		InitialHeight:                     types.Height{RevisionNumber: 2, RevisionHeight: 3},
		GenesisHash:                       []byte{2, 3},
		BinaryHash:                        []byte{4, 5},
		SpawnTime:                         time.Unix(2, 3).UTC(),
		UnbondingPeriod:                   time.Duration(789),
		CcvTimeoutPeriod:                  time.Duration(101112),
		TransferTimeoutPeriod:             time.Duration(131415),
		ConsumerRedistributionFraction:    "consumer_redistribution_fraction2",
		BlocksPerDistributionTransmission: 456,
		HistoricalEntries:                 789,
		DistributionTransmissionChannel:   "distribution_transmission_channel2",
	}
	providerKeeper.SetConsumerInitializationParameters(ctx, "consumerId", expectedInitializationParameters)
	actualInitializationParameters, err = providerKeeper.GetConsumerInitializationParameters(ctx, "consumerId")
	require.NoError(t, err)
	require.Equal(t, expectedInitializationParameters, actualInitializationParameters)

	providerKeeper.DeleteConsumerInitializationParameters(ctx, "consumerId")
	actualInitializationParameters, err = providerKeeper.GetConsumerInitializationParameters(ctx, "consumerId")
	require.Error(t, err)
	require.Equal(t, providertypes.ConsumerInitializationParameters{}, actualInitializationParameters)
}

// TestConsumerPowerShapingParameters tests the getter, setter, and deletion of the consumer id to power-shaping parameters methods
func TestConsumerPowerShapingParameters(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	_, err := providerKeeper.GetConsumerPowerShapingParameters(ctx, "consumerId")
	require.Error(t, err)

	expectedPowerShapingParameters := providertypes.PowerShapingParameters{
		Top_N:              10,
		ValidatorsPowerCap: 34,
		ValidatorSetCap:    10,
		Allowlist:          []string{"allowlist1", "allowlist2"},
		Denylist:           []string{"denylist1", "denylist2"},
		MinStake:           234,
		AllowInactiveVals:  true,
	}
	providerKeeper.SetConsumerPowerShapingParameters(ctx, "consumerId", expectedPowerShapingParameters)
	actualPowerShapingParameters, err := providerKeeper.GetConsumerPowerShapingParameters(ctx, "consumerId")
	require.NoError(t, err)
	require.Equal(t, expectedPowerShapingParameters, actualPowerShapingParameters)

	// assert that overwriting the current initialization record works
	expectedPowerShapingParameters = providertypes.PowerShapingParameters{
		Top_N:              12,
		ValidatorsPowerCap: 67,
		ValidatorSetCap:    20,
		Allowlist:          []string{"allowlist3", "allowlist4"},
		Denylist:           []string{"denylist3", "denylist4"},
		MinStake:           567,
		AllowInactiveVals:  false,
	}
	providerKeeper.SetConsumerPowerShapingParameters(ctx, "consumerId", expectedPowerShapingParameters)
	actualPowerShapingParameters, err = providerKeeper.GetConsumerPowerShapingParameters(ctx, "consumerId")
	require.NoError(t, err)
	require.Equal(t, expectedPowerShapingParameters, actualPowerShapingParameters)

	providerKeeper.DeleteConsumerPowerShapingParameters(ctx, "consumerId")
	actualPowerShapingParameters, err = providerKeeper.GetConsumerPowerShapingParameters(ctx, "consumerId")
	require.Error(t, err)
	require.Equal(t, providertypes.PowerShapingParameters{}, actualPowerShapingParameters)
}

// TestConsumerPhase tests the getter, setter, and deletion of the consumer id to phase methods
func TestConsumerPhase(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	phase := providerKeeper.GetConsumerPhase(ctx, "consumerId")
	require.Equal(t, providertypes.ConsumerPhase_CONSUMER_PHASE_UNSPECIFIED, phase)

	providerKeeper.SetConsumerPhase(ctx, "consumerId", providertypes.ConsumerPhase_CONSUMER_PHASE_INITIALIZED)
	phase = providerKeeper.GetConsumerPhase(ctx, "consumerId")
	require.Equal(t, providertypes.ConsumerPhase_CONSUMER_PHASE_INITIALIZED, phase)

	providerKeeper.SetConsumerPhase(ctx, "consumerId", providertypes.ConsumerPhase_CONSUMER_PHASE_LAUNCHED)
	phase = providerKeeper.GetConsumerPhase(ctx, "consumerId")
	require.Equal(t, providertypes.ConsumerPhase_CONSUMER_PHASE_LAUNCHED, phase)
}

// TestConsumerStopTime tests the getter, setter, and deletion of the consumer id to stop times methods
func TestConsumerStopTime(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	_, err := providerKeeper.GetConsumerStopTime(ctx, "consumerId")
	require.Error(t, err)

	expectedStopTime := time.Unix(1234, 56789)
	providerKeeper.SetConsumerStopTime(ctx, "consumerId", expectedStopTime)
	actualStopTime, err := providerKeeper.GetConsumerStopTime(ctx, "consumerId")
	require.NoError(t, err)
	require.Equal(t, actualStopTime, expectedStopTime)

	providerKeeper.DeleteConsumerStopTime(ctx, "consumerId")
	_, err = providerKeeper.GetConsumerStopTime(ctx, "consumerId")
	require.Error(t, err)
}

// TestConsumersToBeLaunched tests `AppendConsumerToBeLaunchedOnSpawnTime`, `GetConsumersToBeLaunched`, and `RemoveConsumerToBeLaunchedFromSpawnTime`
func TestConsumersToBeLaunched(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	spawnTime := time.Now()
	providerKeeper.AppendConsumerToBeLaunchedOnSpawnTime(ctx, "consumerId1", spawnTime)
	consumers, err := providerKeeper.GetConsumersToBeLaunched(ctx, spawnTime)
	require.NoError(t, err)
	require.Equal(t, []string{"consumerId1"}, consumers.Ids)

	providerKeeper.AppendConsumerToBeLaunchedOnSpawnTime(ctx, "consumerId2", spawnTime)
	consumers, err = providerKeeper.GetConsumersToBeLaunched(ctx, spawnTime)
	require.NoError(t, err)
	require.Equal(t, []string{"consumerId1", "consumerId2"}, consumers.Ids)

	providerKeeper.AppendConsumerToBeLaunchedOnSpawnTime(ctx, "consumerId3", spawnTime)
	consumers, err = providerKeeper.GetConsumersToBeLaunched(ctx, spawnTime)
	require.NoError(t, err)
	require.Equal(t, []string{"consumerId1", "consumerId2", "consumerId3"}, consumers.Ids)

	err = providerKeeper.RemoveConsumerToBeLaunchedFromSpawnTime(ctx, "consumerId2", spawnTime)
	require.NoError(t, err)
	consumers, err = providerKeeper.GetConsumersToBeLaunched(ctx, spawnTime)
	require.NoError(t, err)
	require.Equal(t, []string{"consumerId1", "consumerId3"}, consumers.Ids)

	// also add consumer ids under a different spawn time and verify everything under the original spawn time is still there
	spawnTimePlusOneHour := spawnTime.Add(time.Hour)
	providerKeeper.AppendConsumerToBeLaunchedOnSpawnTime(ctx, "consumerId4", spawnTimePlusOneHour)
	consumers, err = providerKeeper.GetConsumersToBeLaunched(ctx, spawnTimePlusOneHour)
	require.NoError(t, err)
	require.Equal(t, []string{"consumerId4"}, consumers.Ids)

	consumers, err = providerKeeper.GetConsumersToBeLaunched(ctx, spawnTime)
	require.NoError(t, err)
	require.Equal(t, []string{"consumerId1", "consumerId3"}, consumers.Ids)

	// start removing all consumers from `spawnTime`
	err = providerKeeper.RemoveConsumerToBeLaunchedFromSpawnTime(ctx, "consumerId3", spawnTime)
	require.NoError(t, err)
	err = providerKeeper.RemoveConsumerToBeLaunchedFromSpawnTime(ctx, "consumerId1", spawnTime)
	require.NoError(t, err)
	consumers, err = providerKeeper.GetConsumersToBeLaunched(ctx, spawnTime)
	require.NoError(t, err)
	require.Empty(t, consumers.Ids)

	// remove from `spawnTimePlusOneHour`
	err = providerKeeper.RemoveConsumerToBeLaunchedFromSpawnTime(ctx, "consumerId4", spawnTimePlusOneHour)
	require.NoError(t, err)
	consumers, err = providerKeeper.GetConsumersToBeLaunched(ctx, spawnTimePlusOneHour)
	require.NoError(t, err)
	require.Empty(t, consumers.Ids)

	// add another consumer for `spawnTime`
	err = providerKeeper.AppendConsumerToBeLaunchedOnSpawnTime(ctx, "consumerId5", spawnTime)
	require.NoError(t, err)
	consumers, err = providerKeeper.GetConsumersToBeLaunched(ctx, spawnTime)
	require.NoError(t, err)
	require.Equal(t, []string{"consumerId5"}, consumers.Ids)
}

// TestConsumersToBeStopped tests `AppendConsumerToBeLaunchedOnSpawnTime`, `GetConsumersToBeLaunched`, and `RemoveConsumerToBeLaunchedFromSpawnTime`
func TestConsumersToBeStopped(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	stopTime := time.Now()
	providerKeeper.AppendConsumerToBeStoppedOnStopTime(ctx, "consumerId1", stopTime)
	consumers, err := providerKeeper.GetConsumersToBeStopped(ctx, stopTime)
	require.NoError(t, err)
	require.Equal(t, []string{"consumerId1"}, consumers.Ids)

	providerKeeper.AppendConsumerToBeStoppedOnStopTime(ctx, "consumerId2", stopTime)
	consumers, err = providerKeeper.GetConsumersToBeStopped(ctx, stopTime)
	require.NoError(t, err)
	require.Equal(t, []string{"consumerId1", "consumerId2"}, consumers.Ids)

	providerKeeper.AppendConsumerToBeStoppedOnStopTime(ctx, "consumerId3", stopTime)
	consumers, err = providerKeeper.GetConsumersToBeStopped(ctx, stopTime)
	require.NoError(t, err)
	require.Equal(t, []string{"consumerId1", "consumerId2", "consumerId3"}, consumers.Ids)

	err = providerKeeper.RemoveConsumerToBeStoppedFromStopTime(ctx, "consumerId2", stopTime)
	require.NoError(t, err)
	consumers, err = providerKeeper.GetConsumersToBeStopped(ctx, stopTime)
	require.NoError(t, err)
	require.Equal(t, []string{"consumerId1", "consumerId3"}, consumers.Ids)

	// also add consumer ids under a different stop time and verify everything under the original stop time is still there
	stopTimePlusOneHour := stopTime.Add(time.Hour)
	providerKeeper.AppendConsumerToBeStoppedOnStopTime(ctx, "consumerId4", stopTimePlusOneHour)
	consumers, err = providerKeeper.GetConsumersToBeStopped(ctx, stopTimePlusOneHour)
	require.NoError(t, err)
	require.Equal(t, []string{"consumerId4"}, consumers.Ids)

	consumers, err = providerKeeper.GetConsumersToBeStopped(ctx, stopTime)
	require.NoError(t, err)
	require.Equal(t, []string{"consumerId1", "consumerId3"}, consumers.Ids)

	// start removing all consumers from `stopTime`
	err = providerKeeper.RemoveConsumerToBeStoppedFromStopTime(ctx, "consumerId3", stopTime)
	require.NoError(t, err)
	err = providerKeeper.RemoveConsumerToBeStoppedFromStopTime(ctx, "consumerId1", stopTime)
	require.NoError(t, err)
	consumers, err = providerKeeper.GetConsumersToBeStopped(ctx, stopTime)
	require.NoError(t, err)
	require.Empty(t, consumers.Ids)

	// remove from `stopTimePlusOneHour`
	err = providerKeeper.RemoveConsumerToBeStoppedFromStopTime(ctx, "consumerId4", stopTimePlusOneHour)
	require.NoError(t, err)
	consumers, err = providerKeeper.GetConsumersToBeStopped(ctx, stopTimePlusOneHour)
	require.NoError(t, err)
	require.Empty(t, consumers.Ids)

	// add another consumer for `stopTime`
	err = providerKeeper.AppendConsumerToBeStoppedOnStopTime(ctx, "consumerId5", stopTime)
	require.NoError(t, err)
	consumers, err = providerKeeper.GetConsumersToBeStopped(ctx, stopTime)
	require.NoError(t, err)
	require.Equal(t, []string{"consumerId5"}, consumers.Ids)
}

// TestOptedInConsumerIds tests the `GetOptedInConsumerIds`, `AppendOptedInConsumerId`, and `RemoveOptedInConsumerId` methods
func TestGetOptedInConsumerIds(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	providerAddr := providertypes.NewProviderConsAddress([]byte("providerAddr"))
	consumers, err := providerKeeper.GetOptedInConsumerIds(ctx, providerAddr)
	require.NoError(t, err)
	require.Empty(t, consumers)

	err = providerKeeper.AppendOptedInConsumerId(ctx, providerAddr, "consumerId1")
	require.NoError(t, err)
	consumers, err = providerKeeper.GetOptedInConsumerIds(ctx, providerAddr)
	require.NoError(t, err)
	require.Equal(t, providertypes.ConsumerIds{
		Ids: []string{"consumerId1"},
	}, consumers)

	err = providerKeeper.AppendOptedInConsumerId(ctx, providerAddr, "consumerId2")
	require.NoError(t, err)
	consumers, err = providerKeeper.GetOptedInConsumerIds(ctx, providerAddr)
	require.NoError(t, err)
	require.Equal(t, providertypes.ConsumerIds{
		Ids: []string{"consumerId1", "consumerId2"},
	}, consumers)

	err = providerKeeper.AppendOptedInConsumerId(ctx, providerAddr, "consumerId3")
	require.NoError(t, err)
	consumers, err = providerKeeper.GetOptedInConsumerIds(ctx, providerAddr)
	require.NoError(t, err)
	require.Equal(t, providertypes.ConsumerIds{
		Ids: []string{"consumerId1", "consumerId2", "consumerId3"},
	}, consumers)

	// remove all the consumer ids
	err = providerKeeper.RemoveOptedInConsumerId(ctx, providerAddr, "consumerId2")
	require.NoError(t, err)
	consumers, err = providerKeeper.GetOptedInConsumerIds(ctx, providerAddr)
	require.NoError(t, err)
	require.Equal(t, providertypes.ConsumerIds{
		Ids: []string{"consumerId1", "consumerId3"},
	}, consumers)

	err = providerKeeper.RemoveOptedInConsumerId(ctx, providerAddr, "consumerId3")
	require.NoError(t, err)

	err = providerKeeper.RemoveOptedInConsumerId(ctx, providerAddr, "consumerId1")
	require.NoError(t, err)

	consumers, err = providerKeeper.GetOptedInConsumerIds(ctx, providerAddr)
	require.NoError(t, err)
	require.Empty(t, consumers)
}

// TestConsumerChainId tests the getter, setter, and deletion of the client id to consumer id methods
func TestClientIdToConsumerId(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	_, found := providerKeeper.GetClientIdToConsumerId(ctx, "clientId")
	require.False(t, found)

	providerKeeper.SetClientIdToConsumerId(ctx, "clientId", "consumerId")
	consumerId, found := providerKeeper.GetClientIdToConsumerId(ctx, "clientId")
	require.True(t, found)
	require.Equal(t, "consumerId", consumerId)

	// assert that overwriting the current consumer id record works
	providerKeeper.SetClientIdToConsumerId(ctx, "clientId", "consumerId2")
	consumerId, found = providerKeeper.GetClientIdToConsumerId(ctx, "clientId")
	require.True(t, found)
	require.Equal(t, "consumerId2", consumerId)

	providerKeeper.DeleteClientIdToConsumerId(ctx, "clientId")
	consumerId, found = providerKeeper.GetClientIdToConsumerId(ctx, "clientId")
	require.False(t, found)
	require.Equal(t, "", consumerId)
}

// TestGetInitializedConsumersReadyToLaunch tests that the ready to-be-launched consumer chains are returned
func TestGetInitializedConsumersReadyToLaunch(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// no chains to-be-launched exist
	require.Empty(t, providerKeeper.GetInitializedConsumersReadyToLaunch(ctx, 5))

	providerKeeper.AppendConsumerToBeLaunchedOnSpawnTime(ctx, "consumerId1", time.Unix(10, 0))
	providerKeeper.AppendConsumerToBeLaunchedOnSpawnTime(ctx, "consumerId2", time.Unix(20, 0))
	providerKeeper.AppendConsumerToBeLaunchedOnSpawnTime(ctx, "consumerId3", time.Unix(30, 0))

	// time has not yet reached the spawn time of "consumerId1"
	ctx = ctx.WithBlockTime(time.Unix(9, 999999999))
	require.Empty(t, providerKeeper.GetInitializedConsumersReadyToLaunch(ctx, 3))

	// time has reached the spawn time of "consumerId1"
	ctx = ctx.WithBlockTime(time.Unix(10, 0))
	require.Equal(t, []string{"consumerId1"}, providerKeeper.GetInitializedConsumersReadyToLaunch(ctx, 3))

	// time has reached the spawn time of "consumerId1" and "consumerId2"
	ctx = ctx.WithBlockTime(time.Unix(20, 0))
	require.Equal(t, []string{"consumerId1", "consumerId2"}, providerKeeper.GetInitializedConsumersReadyToLaunch(ctx, 3))

	// time has reached the spawn time of all chains
	ctx = ctx.WithBlockTime(time.Unix(30, 0))
	require.Equal(t, []string{"consumerId1", "consumerId2", "consumerId3"}, providerKeeper.GetInitializedConsumersReadyToLaunch(ctx, 3))

	// limit the number of returned consumer chains
	require.Equal(t, []string{}, providerKeeper.GetInitializedConsumersReadyToLaunch(ctx, 0))
	require.Equal(t, []string{"consumerId1"}, providerKeeper.GetInitializedConsumersReadyToLaunch(ctx, 1))
	require.Equal(t, []string{"consumerId1", "consumerId2"}, providerKeeper.GetInitializedConsumersReadyToLaunch(ctx, 2))
}

func TestGetLaunchedConsumersReadyToStop(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// no chains to-be-stopped exist
	require.Empty(t, providerKeeper.GetLaunchedConsumersReadyToStop(ctx, 3))

	providerKeeper.AppendConsumerToBeStoppedOnStopTime(ctx, "consumerId1", time.Unix(10, 0))
	providerKeeper.AppendConsumerToBeStoppedOnStopTime(ctx, "consumerId2", time.Unix(20, 0))
	providerKeeper.AppendConsumerToBeStoppedOnStopTime(ctx, "consumerId3", time.Unix(30, 0))

	// time has not yet reached the stop time of "consumerId1"
	ctx = ctx.WithBlockTime(time.Unix(9, 999999999))
	require.Empty(t, providerKeeper.GetLaunchedConsumersReadyToStop(ctx, 3))

	// time has reached the stop time of "consumerId1"
	ctx = ctx.WithBlockTime(time.Unix(10, 0))
	require.Equal(t, []string{"consumerId1"}, providerKeeper.GetLaunchedConsumersReadyToStop(ctx, 3))

	// time has reached the stop time of "consumerId1" and "consumerId2"
	ctx = ctx.WithBlockTime(time.Unix(20, 0))
	require.Equal(t, []string{"consumerId1", "consumerId2"}, providerKeeper.GetLaunchedConsumersReadyToStop(ctx, 3))

	// time has reached the stop time of all chains
	ctx = ctx.WithBlockTime(time.Unix(30, 0))
	require.Equal(t, []string{"consumerId1", "consumerId2", "consumerId3"}, providerKeeper.GetLaunchedConsumersReadyToStop(ctx, 3))
}

func TestUpdateAllowlist(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerId := "0"

	providerConsAddr1 := "cosmosvalcons1qmq08eruchr5sf5s3rwz7djpr5a25f7xw4mceq"
	consAddr1, _ := sdk.ConsAddressFromBech32(providerConsAddr1)
	providerConsAddr2 := "cosmosvalcons1nx7n5uh0ztxsynn4sje6eyq2ud6rc6klc96w39"
	consAddr2, _ := sdk.ConsAddressFromBech32(providerConsAddr2)

	providerKeeper.UpdateAllowlist(ctx, consumerId, []string{providerConsAddr1, providerConsAddr2})

	expectedAllowlist := []providertypes.ProviderConsAddress{
		providertypes.NewProviderConsAddress(consAddr1),
		providertypes.NewProviderConsAddress(consAddr2)}
	require.Equal(t, expectedAllowlist, providerKeeper.GetAllowList(ctx, consumerId))
}

func TestUpdateDenylist(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerId := "0"

	providerConsAddr1 := "cosmosvalcons1qmq08eruchr5sf5s3rwz7djpr5a25f7xw4mceq"
	consAddr1, _ := sdk.ConsAddressFromBech32(providerConsAddr1)
	providerConsAddr2 := "cosmosvalcons1nx7n5uh0ztxsynn4sje6eyq2ud6rc6klc96w39"
	consAddr2, _ := sdk.ConsAddressFromBech32(providerConsAddr2)

	providerKeeper.UpdateDenylist(ctx, consumerId, []string{providerConsAddr1, providerConsAddr2})

	expectedDenylist := []providertypes.ProviderConsAddress{
		providertypes.NewProviderConsAddress(consAddr1),
		providertypes.NewProviderConsAddress(consAddr2)}
	require.Equal(t, expectedDenylist, providerKeeper.GetDenyList(ctx, consumerId))
}

func TestUpdateMinimumPowerInTopN(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerId := "0"

	// test case where Top N is 0 in which case there's no minimum power in top N
	providerKeeper.SetConsumerPowerShapingParameters(ctx, consumerId, providertypes.PowerShapingParameters{
		Top_N: 0,
	})

	err := providerKeeper.UpdateMinimumPowerInTopN(ctx, consumerId, 0, 0)
	require.NoError(t, err)
	_, found := providerKeeper.GetMinimumPowerInTopN(ctx, consumerId)
	require.False(t, found)

	// test cases where Top N > 0 and for this we mock some validators
	powers := []int64{10, 20, 30}
	validators := []stakingtypes.Validator{
		createStakingValidator(ctx, mocks, 1, powers[0], 1), // this validator has ~16 of the total voting power
		createStakingValidator(ctx, mocks, 2, powers[1], 2), // this validator has ~33% of the total voting gpower
		createStakingValidator(ctx, mocks, 3, powers[2], 3), // this validator has 50% of the total voting power
	}
	mocks.MockStakingKeeper.EXPECT().GetBondedValidatorsByPower(gomock.Any()).Return(validators, nil).AnyTimes()

	maxProviderConsensusValidators := int64(3)
	params := providerKeeper.GetParams(ctx)
	params.MaxProviderConsensusValidators = maxProviderConsensusValidators
	providerKeeper.SetParams(ctx, params)

	// when top N is 50, the minimum power is 30 (because top validator has to validate)
	providerKeeper.SetConsumerPowerShapingParameters(ctx, consumerId, providertypes.PowerShapingParameters{
		Top_N: 50,
	})
	err = providerKeeper.UpdateMinimumPowerInTopN(ctx, consumerId, 0, 50)
	require.NoError(t, err)
	minimumPowerInTopN, found := providerKeeper.GetMinimumPowerInTopN(ctx, consumerId)
	require.True(t, found)
	require.Equal(t, int64(30), minimumPowerInTopN)

	// when top N is 51, the minimum power is 20 (because top 2 validators have to validate)
	providerKeeper.SetConsumerPowerShapingParameters(ctx, consumerId, providertypes.PowerShapingParameters{
		Top_N: 51,
	})
	err = providerKeeper.UpdateMinimumPowerInTopN(ctx, consumerId, 50, 51)
	require.NoError(t, err)
	minimumPowerInTopN, found = providerKeeper.GetMinimumPowerInTopN(ctx, consumerId)
	require.True(t, found)
	require.Equal(t, int64(20), minimumPowerInTopN)

	// when top N is 100, the minimum power is 10 (that of the validator with the lowest power)
	providerKeeper.SetConsumerPowerShapingParameters(ctx, consumerId, providertypes.PowerShapingParameters{
		Top_N: 100,
	})
	err = providerKeeper.UpdateMinimumPowerInTopN(ctx, consumerId, 51, 100)
	require.NoError(t, err)
	minimumPowerInTopN, found = providerKeeper.GetMinimumPowerInTopN(ctx, consumerId)
	require.True(t, found)
	require.Equal(t, int64(10), minimumPowerInTopN)
}

func TestIsValidatorOptedInToChain(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	chainId := "chainId"
	providerAddr := providertypes.NewProviderConsAddress([]byte("providerAddr"))
	_, found := providerKeeper.IsValidatorOptedInToChainId(ctx, providerAddr, chainId)
	require.False(t, found)

	expectedConsumerId := "consumerId"
	providerKeeper.SetConsumerChainId(ctx, expectedConsumerId, chainId)
	providerKeeper.SetOptedIn(ctx, expectedConsumerId, providerAddr)
	providerKeeper.AppendOptedInConsumerId(ctx, providerAddr, expectedConsumerId)
	actualConsumerId, found := providerKeeper.IsValidatorOptedInToChainId(ctx, providerAddr, chainId)
	require.True(t, found)
	require.Equal(t, expectedConsumerId, actualConsumerId)
}

func TestPrepareConsumerForLaunch(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	spawnTime := time.Now().UTC()
	err := providerKeeper.PrepareConsumerForLaunch(ctx, "consumerId", time.Time{}, spawnTime)
	require.NoError(t, err)

	consumers, err := providerKeeper.GetConsumersToBeLaunched(ctx, spawnTime)
	require.NoError(t, err)
	require.Equal(t, providertypes.ConsumerIds{Ids: []string{"consumerId"}}, consumers)

	nextSpawnTime := spawnTime.Add(time.Hour)
	err = providerKeeper.PrepareConsumerForLaunch(ctx, "consumerId", spawnTime, nextSpawnTime)
	require.NoError(t, err)

	consumers, err = providerKeeper.GetConsumersToBeLaunched(ctx, spawnTime)
	require.NoError(t, err)
	require.Empty(t, consumers)

	consumers, err = providerKeeper.GetConsumersToBeLaunched(ctx, nextSpawnTime)
	require.NoError(t, err)
	require.Equal(t, providertypes.ConsumerIds{Ids: []string{"consumerId"}}, consumers)
}

func TestCanLaunch(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// cannot launch an unknown chain
	_, canLaunch := providerKeeper.CanLaunch(ctx, "consumerId")
	require.False(t, canLaunch)

	// cannot launch a chain without initialization parameters
	providerKeeper.SetConsumerPhase(ctx, "consumerId", providertypes.ConsumerPhase_CONSUMER_PHASE_INITIALIZED)
	_, canLaunch = providerKeeper.CanLaunch(ctx, "consumerId")
	require.False(t, canLaunch)

	// set valid initialization parameters
	initializationParameters := testkeeper.GetTestInitializationParameters()
	err := providerKeeper.SetConsumerInitializationParameters(ctx, "consumerId", initializationParameters)
	require.NoError(t, err)

	// cannot launch a launched chain
	providerKeeper.SetConsumerPhase(ctx, "consumerId", providertypes.ConsumerPhase_CONSUMER_PHASE_LAUNCHED)
	_, canLaunch = providerKeeper.CanLaunch(ctx, "consumerId")
	require.False(t, canLaunch)

	// cannot launch a stopped chain
	providerKeeper.SetConsumerPhase(ctx, "consumerId", providertypes.ConsumerPhase_CONSUMER_PHASE_STOPPED)
	_, canLaunch = providerKeeper.CanLaunch(ctx, "consumerId")
	require.False(t, canLaunch)

	// initialized chain can launch
	providerKeeper.SetConsumerPhase(ctx, "consumerId", providertypes.ConsumerPhase_CONSUMER_PHASE_INITIALIZED)
	_, canLaunch = providerKeeper.CanLaunch(ctx, "consumerId")
	require.True(t, canLaunch)

	// chain cannot launch without a genesis hash
	initializationParameters.GenesisHash = nil
	err = providerKeeper.SetConsumerInitializationParameters(ctx, "consumerId", initializationParameters)
	_, canLaunch = providerKeeper.CanLaunch(ctx, "consumerId")
	require.NoError(t, err)
	require.False(t, canLaunch)
}

func TestHasAtMostOnceCorrectMsgUpdateConsumer(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	expectedMsgUpdateConsumer := providertypes.MsgUpdateConsumer{Signer: "signer", ConsumerId: "consumerId", NewOwnerAddress: "new owner address"}

	proposal, err := govv1.NewProposal([]sdk.Msg{&expectedMsgUpdateConsumer}, 1, time.Now(), time.Now().Add(1*time.Hour), "metadata", "title", "summary", sdk.AccAddress{}, false)
	require.NoError(t, err)

	_, err = providerKeeper.HasAtMostOnceCorrectMsgUpdateConsumer(ctx, &proposal)
	require.ErrorContains(t, err, "cannot find owner address")

	// set owner address that is not the gov module
	providerKeeper.SetConsumerOwnerAddress(ctx, "consumerId", "owner address")
	_, err = providerKeeper.HasAtMostOnceCorrectMsgUpdateConsumer(ctx, &proposal)
	require.ErrorContains(t, err, "is not the gov module")

	// set owner address that is the gov module
	providerKeeper.SetConsumerOwnerAddress(ctx, "consumerId", "cosmos10d07y265gmmuvt4z0w9aw880jnsr700j6zn9kn")
	actualMsgUpdateConsumer, err := providerKeeper.HasAtMostOnceCorrectMsgUpdateConsumer(ctx, &proposal)
	require.NoError(t, err)
	require.Equal(t, expectedMsgUpdateConsumer, *actualMsgUpdateConsumer)

	// a proposal with 2 `MsgUpdateConsumer` messages
	invalidProposal, err := govv1.NewProposal([]sdk.Msg{&expectedMsgUpdateConsumer, &expectedMsgUpdateConsumer}, 1, time.Now(), time.Now().Add(1*time.Hour), "metadata", "title", "summary", sdk.AccAddress{}, false)
	actualMsgUpdateConsumer, err = providerKeeper.HasAtMostOnceCorrectMsgUpdateConsumer(ctx, &invalidProposal)
	require.ErrorContains(t, err, "proposal can contain at most one")
	require.Nil(t, actualMsgUpdateConsumer)
}

func TestDoesNotHaveDeprecatedMessage(t *testing.T) {
	msgConsumerAddition := providertypes.MsgConsumerAddition{}
	proposal, err := govv1.NewProposal([]sdk.Msg{&msgConsumerAddition}, 1, time.Now(), time.Now().Add(1*time.Hour), "metadata", "title", "summary", sdk.AccAddress{}, false)
	require.NoError(t, err)
	err = keeper.DoesNotHaveDeprecatedMessage(&proposal)
	require.ErrorContains(t, err, "cannot contain deprecated `MsgConsumerAddition`")

	msgConsumerModification := providertypes.MsgConsumerModification{}
	proposal, err = govv1.NewProposal([]sdk.Msg{&msgConsumerModification}, 1, time.Now(), time.Now().Add(1*time.Hour), "metadata", "title", "summary", sdk.AccAddress{}, false)
	require.NoError(t, err)
	err = keeper.DoesNotHaveDeprecatedMessage(&proposal)
	require.ErrorContains(t, err, "cannot contain deprecated `MsgConsumerModification`")

	msgConsumerRemoval := providertypes.MsgConsumerRemoval{}
	proposal, err = govv1.NewProposal([]sdk.Msg{&msgConsumerRemoval}, 1, time.Now(), time.Now().Add(1*time.Hour), "metadata", "title", "summary", sdk.AccAddress{}, false)
	require.NoError(t, err)
	err = keeper.DoesNotHaveDeprecatedMessage(&proposal)
	require.ErrorContains(t, err, "cannot contain deprecated `MsgConsumerRemoval`")

	// a proposal with no deprecated messages
	msgUpdateConsumer := providertypes.MsgUpdateConsumer{Signer: "signer", ConsumerId: "consumerId", NewOwnerAddress: "new owner address"}
	proposal, err = govv1.NewProposal([]sdk.Msg{&msgUpdateConsumer}, 1, time.Now(), time.Now().Add(1*time.Hour), "metadata", "title", "summary", sdk.AccAddress{}, false)
	require.NoError(t, err)
	err = keeper.DoesNotHaveDeprecatedMessage(&proposal)
	require.Nil(t, err)
}
