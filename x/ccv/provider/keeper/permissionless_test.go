package keeper_test

import (
	"github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
	testkeeper "github.com/cosmos/interchain-security/v5/testutil/keeper"
	"github.com/cosmos/interchain-security/v5/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	"github.com/stretchr/testify/require"
	"testing"
	"time"
)

func TestFetchAndIncrementConsumerId(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerId := providerKeeper.FetchAndIncrementConsumerId(ctx)
	require.Equal(t, "0", consumerId)

	consumerId = providerKeeper.FetchAndIncrementConsumerId(ctx)
	require.Equal(t, "1", consumerId)

	consumerId = providerKeeper.FetchAndIncrementConsumerId(ctx)
	require.Equal(t, "2", consumerId)
}

// TestClientIdToConsumerId tests the getter, setter, and deletion methods of the client id to consumer id methods
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

// TestConsumerIdToRegistrationRecord tests the getter, setter, and deletion methods of the consumer id to registration record methods
func TestConsumerIdToRegistrationRecord(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	_, err := providerKeeper.GetConsumerRegistrationRecord(ctx, "consumerId")
	require.Error(t, err)

	expectedRecord := providertypes.ConsumerRegistrationRecord{
		Title:       "title",
		Description: "description",
		ChainId:     "chain_id",
	}
	providerKeeper.SetConsumerRegistrationRecord(ctx, "consumerId", expectedRecord)
	actualRecord, err := providerKeeper.GetConsumerRegistrationRecord(ctx, "consumerId")
	require.NoError(t, err)
	require.Equal(t, expectedRecord, actualRecord)

	// assert that overwriting the current registration record works
	expectedRecord = providertypes.ConsumerRegistrationRecord{
		Title:       "title 2",
		Description: "description 2",
		ChainId:     "chain_id2",
	}
	providerKeeper.SetConsumerRegistrationRecord(ctx, "consumerId", expectedRecord)
	actualRecord, err = providerKeeper.GetConsumerRegistrationRecord(ctx, "consumerId")
	require.NoError(t, err)
	require.Equal(t, expectedRecord, actualRecord)

	providerKeeper.DeleteConsumerRegistrationRecord(ctx, "consumerId")
	actualRecord, err = providerKeeper.GetConsumerRegistrationRecord(ctx, "consumerId")
	require.Error(t, err)
	require.Equal(t, providertypes.ConsumerRegistrationRecord{}, actualRecord)
}

// TestConsumerIdToInitializationRecord tests the getter, setter, and deletion methods of the consumer id to initialization record methods
func TestConsumerIdToInitializationRecord(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	_, err := providerKeeper.GetConsumerInitializationRecord(ctx, "consumerId")
	require.Error(t, err)

	expectedRecord := providertypes.ConsumerInitializationRecord{
		InitialHeight:                     types.Height{RevisionNumber: 1, RevisionHeight: 2},
		GenesisHash:                       []byte{0, 1},
		BinaryHash:                        []byte{2, 3},
		SpawnTime:                         time.Unix(1, 2).UTC(),
		UnbondingPeriod:                   3456,
		CcvTimeoutPeriod:                  789,
		TransferTimeoutPeriod:             101112,
		ConsumerRedistributionFraction:    "consumer_redistribution_fraction",
		BlocksPerDistributionTransmission: 123,
		HistoricalEntries:                 456,
		DistributionTransmissionChannel:   "distribution_transmission_channel",
	}
	providerKeeper.SetConsumerInitializationRecord(ctx, "consumerId", expectedRecord)
	actualRecord, err := providerKeeper.GetConsumerInitializationRecord(ctx, "consumerId")
	require.NoError(t, err)
	require.Equal(t, expectedRecord, actualRecord)

	// assert that overwriting the current initialization record works
	expectedRecord = providertypes.ConsumerInitializationRecord{
		InitialHeight:                     types.Height{RevisionNumber: 2, RevisionHeight: 3},
		GenesisHash:                       []byte{2, 3},
		BinaryHash:                        []byte{4, 5},
		SpawnTime:                         time.Unix(2, 3).UTC(),
		UnbondingPeriod:                   789,
		CcvTimeoutPeriod:                  101112,
		TransferTimeoutPeriod:             131415,
		ConsumerRedistributionFraction:    "consumer_redistribution_fraction2",
		BlocksPerDistributionTransmission: 456,
		HistoricalEntries:                 789,
		DistributionTransmissionChannel:   "distribution_transmission_channel2",
	}
	providerKeeper.SetConsumerInitializationRecord(ctx, "consumerId", expectedRecord)
	actualRecord, err = providerKeeper.GetConsumerInitializationRecord(ctx, "consumerId")
	require.NoError(t, err)
	require.Equal(t, expectedRecord, actualRecord)

	providerKeeper.DeleteConsumerInitializationRecord(ctx, "consumerId")
	actualRecord, err = providerKeeper.GetConsumerInitializationRecord(ctx, "consumerId")
	require.Error(t, err)
	require.Equal(t, providertypes.ConsumerInitializationRecord{}, actualRecord)
}

// TestConsumerIdToOwnerAddress tests the getter, setter, and deletion methods of the owner address to registration record methods
func TestConsumerIdToOwnerAddress(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	providerKeeper.SetConsumerOwnerAddress(ctx, "consumerId", "owner_address")
	address := providerKeeper.GetConsumerOwnerAddress(ctx, "consumerId")
	require.Equal(t, "owner_address", address)

	// assert that overwriting the current owner address works
	providerKeeper.SetConsumerOwnerAddress(ctx, "consumerId", "owner_address2")
	address = providerKeeper.GetConsumerOwnerAddress(ctx, "consumerId")
	require.Equal(t, "owner_address2", address)
}

// TestConsumerIdToPhase tests the getter, setter, and deletion methods of the consumer id to phase methods
func TestConsumerIdToPhase(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	_, found := providerKeeper.GetConsumerPhase(ctx, "consumerId")
	require.False(t, found)

	providerKeeper.SetConsumerPhase(ctx, "consumerId", keeper.Registered)
	phase, found := providerKeeper.GetConsumerPhase(ctx, "consumerId")
	require.True(t, found)
	require.Equal(t, keeper.Registered, phase)

	providerKeeper.SetConsumerPhase(ctx, "consumerId", keeper.Launched)
	phase, found = providerKeeper.GetConsumerPhase(ctx, "consumerId")
	require.True(t, found)
	require.Equal(t, keeper.Launched, phase)
}

// TestConsumerIdToStopTime tests the getter, setter, and deletion methods of the consumer id to stop times
func TestConsumerIdToStopTime(t *testing.T) {
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

// TestGetInitializedConsumersReadyToLaunch tests that the ready to-be-launched consumer chains are returned
func TestGetInitializedConsumersReadyToLaunch(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// no chains to-be-launched exist
	require.Empty(t, providerKeeper.GetInitializedConsumersReadyToLaunch(ctx, 5))

	providerKeeper.AppendSpawnTimeForConsumerToBeLaunched(ctx, "consumerId1", time.Unix(10, 0))
	providerKeeper.AppendSpawnTimeForConsumerToBeLaunched(ctx, "consumerId2", time.Unix(20, 0))
	providerKeeper.AppendSpawnTimeForConsumerToBeLaunched(ctx, "consumerId3", time.Unix(30, 0))

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

	providerKeeper.AppendStopTimeForConsumerToBeStopped(ctx, "consumerId1", time.Unix(10, 0))
	providerKeeper.AppendStopTimeForConsumerToBeStopped(ctx, "consumerId2", time.Unix(20, 0))
	providerKeeper.AppendStopTimeForConsumerToBeStopped(ctx, "consumerId3", time.Unix(30, 0))

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

func TestIsValidatorOptedInToChain(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	chainId := "chainId"
	providerAddr := providertypes.NewProviderConsAddress([]byte("providerAddr"))
	_, found := providerKeeper.IsValidatorOptedInToChainId(ctx, providerAddr, chainId)
	require.False(t, found)

	expectedConsumerId := "consumerId"
	providerKeeper.SetConsumerRegistrationRecord(ctx, expectedConsumerId, providertypes.ConsumerRegistrationRecord{
		ChainId: chainId,
	})
	providerKeeper.SetOptedIn(ctx, expectedConsumerId, providerAddr)
	providerKeeper.AppendOptedInConsumerId(ctx, providerAddr, expectedConsumerId)
	actualConsumerId, found := providerKeeper.IsValidatorOptedInToChainId(ctx, providerAddr, chainId)
	require.True(t, found)
	require.Equal(t, expectedConsumerId, actualConsumerId)
}
