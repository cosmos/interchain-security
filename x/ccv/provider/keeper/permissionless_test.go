package keeper_test

import (
	"testing"
	"time"

	"github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
	"github.com/stretchr/testify/require"

	testkeeper "github.com/cosmos/interchain-security/v6/testutil/keeper"
	providertypes "github.com/cosmos/interchain-security/v6/x/ccv/provider/types"
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

	providerKeeper.SetConsumerOwnerAddress(ctx, CONSUMER_ID, "owner address")
	ownerAddress, err := providerKeeper.GetConsumerOwnerAddress(ctx, CONSUMER_ID)
	require.NoError(t, err)
	require.Equal(t, "owner address", ownerAddress)

	// write under a different key
	providerKeeper.SetConsumerOwnerAddress(ctx, "consumerId2", "owner address")
	ownerAddress, err = providerKeeper.GetConsumerOwnerAddress(ctx, "consumerId2")
	require.NoError(t, err)
	require.Equal(t, "owner address", ownerAddress)

	// assert that overwriting the current key works
	providerKeeper.SetConsumerOwnerAddress(ctx, CONSUMER_ID, "owner address2")
	ownerAddress, err = providerKeeper.GetConsumerOwnerAddress(ctx, CONSUMER_ID)
	require.NoError(t, err)
	require.Equal(t, "owner address2", ownerAddress)

	providerKeeper.DeleteConsumerOwnerAddress(ctx, CONSUMER_ID)
	_, err = providerKeeper.GetConsumerChainId(ctx, CONSUMER_ID)
	require.Error(t, err, "failed to retrieve owner address")
}

// TestConsumerMetadata tests the getter, setter, and deletion of the consumer id to consumer metadata methods
func TestConsumerMetadata(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	_, err := providerKeeper.GetConsumerMetadata(ctx, CONSUMER_ID)
	require.Error(t, err)

	expectedMetadata := providertypes.ConsumerMetadata{
		Name:        "name",
		Description: "description",
		Metadata:    "metadata",
		// ChainId:     "chain_id",
	}
	providerKeeper.SetConsumerMetadata(ctx, CONSUMER_ID, expectedMetadata)
	actualMetadata, err := providerKeeper.GetConsumerMetadata(ctx, CONSUMER_ID)
	require.NoError(t, err)
	require.Equal(t, expectedMetadata, actualMetadata)

	// assert that overwriting the current registration record works
	expectedMetadata = providertypes.ConsumerMetadata{
		Name:        "name 2",
		Description: "description 2",
		Metadata:    "metadata 2",
		// ChainId:     "chain_id2",
	}
	providerKeeper.SetConsumerMetadata(ctx, CONSUMER_ID, expectedMetadata)
	actualMetadata, err = providerKeeper.GetConsumerMetadata(ctx, CONSUMER_ID)
	require.NoError(t, err)
	require.Equal(t, expectedMetadata, actualMetadata)

	providerKeeper.DeleteConsumerMetadata(ctx, CONSUMER_ID)
	actualMetadata, err = providerKeeper.GetConsumerMetadata(ctx, CONSUMER_ID)
	require.Error(t, err)
	require.Equal(t, providertypes.ConsumerMetadata{}, actualMetadata)
}

// TestConsumerInitializationParameters tests the getter, setter, and deletion of the consumer id to initialization parameters methods
func TestConsumerInitializationParameters(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	_, err := providerKeeper.GetConsumerInitializationParameters(ctx, CONSUMER_ID)
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
	providerKeeper.SetConsumerChainId(ctx, CONSUMER_ID, "chain-1")
	err = providerKeeper.SetConsumerInitializationParameters(ctx, CONSUMER_ID, expectedInitializationParameters)
	require.NoError(t, err)
	actualInitializationParameters, err := providerKeeper.GetConsumerInitializationParameters(ctx, CONSUMER_ID)
	require.NoError(t, err)
	require.Equal(t, expectedInitializationParameters, actualInitializationParameters)

	// assert that overwriting the current initialization record works
	expectedInitializationParameters = providertypes.ConsumerInitializationParameters{
		InitialHeight:                     types.Height{RevisionNumber: 1, RevisionHeight: 3},
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
	providerKeeper.SetConsumerInitializationParameters(ctx, CONSUMER_ID, expectedInitializationParameters)
	actualInitializationParameters, err = providerKeeper.GetConsumerInitializationParameters(ctx, CONSUMER_ID)
	require.NoError(t, err)
	require.Equal(t, expectedInitializationParameters, actualInitializationParameters)

	providerKeeper.DeleteConsumerInitializationParameters(ctx, CONSUMER_ID)
	actualInitializationParameters, err = providerKeeper.GetConsumerInitializationParameters(ctx, CONSUMER_ID)
	require.Error(t, err)
	require.Equal(t, providertypes.ConsumerInitializationParameters{}, actualInitializationParameters)
}

// TestConsumerPhase tests the getter, setter, and deletion of the consumer id to phase methods
func TestConsumerPhase(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	phase := providerKeeper.GetConsumerPhase(ctx, CONSUMER_ID)
	require.Equal(t, providertypes.CONSUMER_PHASE_UNSPECIFIED, phase)

	providerKeeper.SetConsumerPhase(ctx, CONSUMER_ID, providertypes.CONSUMER_PHASE_INITIALIZED)
	phase = providerKeeper.GetConsumerPhase(ctx, CONSUMER_ID)
	require.Equal(t, providertypes.CONSUMER_PHASE_INITIALIZED, phase)

	providerKeeper.SetConsumerPhase(ctx, CONSUMER_ID, providertypes.CONSUMER_PHASE_LAUNCHED)
	phase = providerKeeper.GetConsumerPhase(ctx, CONSUMER_ID)
	require.Equal(t, providertypes.CONSUMER_PHASE_LAUNCHED, phase)
}

func TestIsConsumerPrelaunched(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	providerKeeper.SetConsumerPhase(ctx, CONSUMER_ID, providertypes.CONSUMER_PHASE_REGISTERED)
	require.True(t, providerKeeper.IsConsumerPrelaunched(ctx, CONSUMER_ID))

	providerKeeper.SetConsumerPhase(ctx, CONSUMER_ID, providertypes.CONSUMER_PHASE_INITIALIZED)
	require.True(t, providerKeeper.IsConsumerPrelaunched(ctx, CONSUMER_ID))

	providerKeeper.SetConsumerPhase(ctx, CONSUMER_ID, providertypes.CONSUMER_PHASE_LAUNCHED)
	require.False(t, providerKeeper.IsConsumerPrelaunched(ctx, CONSUMER_ID))

	providerKeeper.SetConsumerPhase(ctx, CONSUMER_ID, providertypes.CONSUMER_PHASE_STOPPED)
	require.False(t, providerKeeper.IsConsumerPrelaunched(ctx, CONSUMER_ID))

	providerKeeper.SetConsumerPhase(ctx, CONSUMER_ID, providertypes.CONSUMER_PHASE_DELETED)
	require.False(t, providerKeeper.IsConsumerPrelaunched(ctx, CONSUMER_ID))
}
