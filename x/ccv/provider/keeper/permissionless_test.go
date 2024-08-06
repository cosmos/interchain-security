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

// TestConsumerId tests methods for retrieving and incrementing consumer id
func TestConsumerId(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerId, found := providerKeeper.GetConsumerId(ctx)
	require.False(t, found)

	consumerId = providerKeeper.FetchAndIncrementConsumerId(ctx)
	require.Equal(t, uint64(0), consumerId)

	consumerId, found = providerKeeper.GetConsumerId(ctx)
	require.True(t, found)
	require.Equal(t, uint64(1), consumerId)

	consumerId = providerKeeper.FetchAndIncrementConsumerId(ctx)
	require.Equal(t, uint64(1), consumerId)

	consumerId, found = providerKeeper.GetConsumerId(ctx)
	require.True(t, found)
	require.Equal(t, uint64(2), consumerId)
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

	_, found := providerKeeper.GetConsumerIdToRegistrationRecord(ctx, "consumerId")
	require.False(t, found)

	expectedRecord := providertypes.ConsumerRegistrationRecord{
		Title:       "title",
		Description: "description",
		ChainId:     "chain_id",
	}
	providerKeeper.SetConsumerIdToRegistrationRecord(ctx, "consumerId", expectedRecord)
	actualRecord, found := providerKeeper.GetConsumerIdToRegistrationRecord(ctx, "consumerId")
	require.True(t, found)
	require.Equal(t, expectedRecord, actualRecord)

	// assert that overwriting the current registration record works
	expectedRecord = providertypes.ConsumerRegistrationRecord{
		Title:       "title 2",
		Description: "description 2",
		ChainId:     "chain_id2",
	}
	providerKeeper.SetConsumerIdToRegistrationRecord(ctx, "consumerId", expectedRecord)
	actualRecord, found = providerKeeper.GetConsumerIdToRegistrationRecord(ctx, "consumerId")
	require.True(t, found)
	require.Equal(t, expectedRecord, actualRecord)

	providerKeeper.DeleteConsumerIdToRegistrationRecord(ctx, "consumerId")
	actualRecord, found = providerKeeper.GetConsumerIdToRegistrationRecord(ctx, "consumerId")
	require.False(t, found)
	require.Equal(t, providertypes.ConsumerRegistrationRecord{}, actualRecord)
}

// TestConsumerIdToInitializationRecord tests the getter, setter, and deletion methods of the consumer id to initialization record methods
func TestConsumerIdToInitializationRecord(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	_, found := providerKeeper.GetConsumerIdToInitializationRecord(ctx, "consumerId")
	require.False(t, found)

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
	providerKeeper.SetConsumerIdToInitializationRecord(ctx, "consumerId", expectedRecord)
	actualRecord, found := providerKeeper.GetConsumerIdToInitializationRecord(ctx, "consumerId")
	require.True(t, found)
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
	providerKeeper.SetConsumerIdToInitializationRecord(ctx, "consumerId", expectedRecord)
	actualRecord, found = providerKeeper.GetConsumerIdToInitializationRecord(ctx, "consumerId")
	require.True(t, found)
	require.Equal(t, expectedRecord, actualRecord)

	providerKeeper.DeleteConsumerIdToInitializationRecord(ctx, "consumerId")
	actualRecord, found = providerKeeper.GetConsumerIdToInitializationRecord(ctx, "consumerId")
	require.False(t, found)
	require.Equal(t, providertypes.ConsumerInitializationRecord{}, actualRecord)
}

// TestConsumerIdToOwnerAddress tests the getter, setter, and deletion methods of the owner address to registration record methods
func TestConsumerIdToOwnerAddress(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	_, found := providerKeeper.GetConsumerIdToOwnerAddress(ctx, "consumerId")
	require.False(t, found)

	providerKeeper.SetConsumerIdToOwnerAddress(ctx, "consumerId", "owner_address")
	address, found := providerKeeper.GetConsumerIdToOwnerAddress(ctx, "consumerId")
	require.True(t, found)
	require.Equal(t, "owner_address", address)

	// assert that overwriting the current owner address works
	providerKeeper.SetConsumerIdToOwnerAddress(ctx, "consumerId", "owner_address2")
	address, found = providerKeeper.GetConsumerIdToOwnerAddress(ctx, "consumerId")
	require.True(t, found)
	require.Equal(t, "owner_address2", address)

	providerKeeper.DeleteConsumerIdToOwnerAddress(ctx, "consumerId")
	_, found = providerKeeper.GetConsumerIdToOwnerAddress(ctx, "consumerId")
	require.False(t, found)
}

// TestConsumerIdToPhase tests the getter, setter, and deletion methods of the consumer id to phase methods
func TestConsumerIdToPhase(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	_, found := providerKeeper.GetConsumerIdToPhase(ctx, "consumerId")
	require.False(t, found)

	providerKeeper.SetConsumerIdToPhase(ctx, "consumerId", keeper.Registered)
	phase, found := providerKeeper.GetConsumerIdToPhase(ctx, "consumerId")
	require.True(t, found)
	require.Equal(t, keeper.Registered, phase)

	providerKeeper.SetConsumerIdToPhase(ctx, "consumerId", keeper.Launched)
	phase, found = providerKeeper.GetConsumerIdToPhase(ctx, "consumerId")
	require.True(t, found)
	require.Equal(t, keeper.Launched, phase)
}

// TestConsumerIdToStopTime tests the getter, setter, and deletion methods of the consumer id to stop times
func TestConsumerIdToStopTime(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	_, found := providerKeeper.GetConsumerIdToStopTime(ctx, "consumerId")
	require.False(t, found)

	expectedStopTime := time.Unix(1234, 56789)
	providerKeeper.SetConsumerIdToStopTime(ctx, "consumerId", expectedStopTime)
	actualStopTime, found := providerKeeper.GetConsumerIdToStopTime(ctx, "consumerId")
	require.True(t, found)
	require.Equal(t, actualStopTime, expectedStopTime)

	providerKeeper.DeleteConsumerIdToStopTime(ctx, "consumerId")
	_, found = providerKeeper.GetConsumerIdToStopTime(ctx, "consumerId")
	require.False(t, found)
}

// TestGetInitializedConsumersReadyToLaunch tests that the ready to-be-launched consumer chains are returned
func TestGetInitializedConsumersReadyToLaunch(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// no chains to-be-launched exist
	require.Empty(t, providerKeeper.GetInitializedConsumersReadyToLaunch(ctx))

	// set 3 initialization records with different spawn times
	providerKeeper.SetConsumerIdToPhase(ctx, "consumerId1", keeper.Initialized)
	providerKeeper.SetConsumerIdToInitializationRecord(ctx, "consumerId1",
		providertypes.ConsumerInitializationRecord{SpawnTime: time.Unix(10, 0)})
	providerKeeper.SetConsumerIdToPhase(ctx, "consumerId2", keeper.Initialized)
	providerKeeper.SetConsumerIdToInitializationRecord(ctx, "consumerId2",
		providertypes.ConsumerInitializationRecord{SpawnTime: time.Unix(20, 0)})
	providerKeeper.SetConsumerIdToPhase(ctx, "consumerId3", keeper.Initialized)
	providerKeeper.SetConsumerIdToInitializationRecord(ctx, "consumerId3",
		providertypes.ConsumerInitializationRecord{SpawnTime: time.Unix(30, 0)})

	// time has not yet reached the spawn time of "consumerId1"
	ctx = ctx.WithBlockTime(time.Unix(9, 999999999))
	require.Empty(t, providerKeeper.GetInitializedConsumersReadyToLaunch(ctx))

	// time has reached the spawn time of "consumerId1"
	ctx = ctx.WithBlockTime(time.Unix(10, 0))
	require.Equal(t, []string{"consumerId1"}, providerKeeper.GetInitializedConsumersReadyToLaunch(ctx))

	// time has reached the spawn time of "consumerId1" and "consumerId2"
	ctx = ctx.WithBlockTime(time.Unix(20, 0))
	require.Equal(t, []string{"consumerId1", "consumerId2"}, providerKeeper.GetInitializedConsumersReadyToLaunch(ctx))

	// time has reached the spawn time of all chains
	ctx = ctx.WithBlockTime(time.Unix(30, 0))
	require.Equal(t, []string{"consumerId1", "consumerId2", "consumerId3"}, providerKeeper.GetInitializedConsumersReadyToLaunch(ctx))
}

func TestGetLaunchedConsumersReadyToStop(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// no chains to-be-stopped exist
	require.Empty(t, providerKeeper.GetLaunchedConsumersReadyToStop(ctx))

	// set 3 initialization records with different spawn times
	providerKeeper.SetConsumerIdToPhase(ctx, "consumerId1", keeper.Launched)
	providerKeeper.SetConsumerIdToStopTime(ctx, "consumerId1", time.Unix(10, 0))
	providerKeeper.SetConsumerIdToPhase(ctx, "consumerId2", keeper.Launched)
	providerKeeper.SetConsumerIdToStopTime(ctx, "consumerId2", time.Unix(20, 0))
	providerKeeper.SetConsumerIdToPhase(ctx, "consumerId3", keeper.Launched)
	providerKeeper.SetConsumerIdToStopTime(ctx, "consumerId3", time.Unix(30, 0))

	// time has not yet reached the stop time of "consumerId1"
	ctx = ctx.WithBlockTime(time.Unix(9, 999999999))
	require.Empty(t, providerKeeper.GetLaunchedConsumersReadyToStop(ctx))

	// time has reached the stop time of "consumerId1"
	ctx = ctx.WithBlockTime(time.Unix(10, 0))
	require.Equal(t, []string{"consumerId1"}, providerKeeper.GetLaunchedConsumersReadyToStop(ctx))

	// time has reached the stop time of "consumerId1" and "consumerId2"
	ctx = ctx.WithBlockTime(time.Unix(20, 0))
	require.Equal(t, []string{"consumerId1", "consumerId2"}, providerKeeper.GetLaunchedConsumersReadyToStop(ctx))

	// time has reached the stop time of all chains
	ctx = ctx.WithBlockTime(time.Unix(30, 0))
	require.Equal(t, []string{"consumerId1", "consumerId2", "consumerId3"}, providerKeeper.GetLaunchedConsumersReadyToStop(ctx))
}

func TestIsValidatorOptedInToChain(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	chainId := "chainId"
	providerAddr := providertypes.NewProviderConsAddress([]byte("providerAddr"))
	_, found := providerKeeper.IsValidatorOptedInToChain(ctx, providerAddr, chainId)
	require.False(t, found)

	expectedConsumerId := "consumerId"
	providerKeeper.SetConsumerIdToRegistrationRecord(ctx, expectedConsumerId, providertypes.ConsumerRegistrationRecord{
		ChainId: chainId,
	})
	providerKeeper.SetOptedIn(ctx, expectedConsumerId, providerAddr)
	actualConsumerId, found := providerKeeper.IsValidatorOptedInToChain(ctx, providerAddr, chainId)
	require.True(t, found)
	require.Equal(t, expectedConsumerId, actualConsumerId)
}
