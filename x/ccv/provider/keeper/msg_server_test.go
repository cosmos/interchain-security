package keeper_test

import (
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	"github.com/cosmos/cosmos-sdk/codec/address"

	testkeeper "github.com/cosmos/interchain-security/v6/testutil/keeper"
	providerkeeper "github.com/cosmos/interchain-security/v6/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/v6/x/ccv/provider/types"
)

func TestCreateConsumer(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	msgServer := providerkeeper.NewMsgServerImpl(&providerKeeper)

	consumerMetadata := providertypes.ConsumerMetadata{
		Name:        "chain name",
		Description: "description",
	}
	response, err := msgServer.CreateConsumer(ctx,
		&providertypes.MsgCreateConsumer{
			Submitter: "submitter", ChainId: "chainId", Metadata: consumerMetadata,
			InitializationParameters: &providertypes.ConsumerInitializationParameters{},
			PowerShapingParameters:   &providertypes.PowerShapingParameters{},
		})
	require.NoError(t, err)
	require.Equal(t, "0", response.ConsumerId)
	actualMetadata, err := providerKeeper.GetConsumerMetadata(ctx, "0")
	require.NoError(t, err)
	require.Equal(t, consumerMetadata, actualMetadata)
	ownerAddress, err := providerKeeper.GetConsumerOwnerAddress(ctx, "0")
	require.NoError(t, err)
	require.Equal(t, "submitter", ownerAddress)
	phase := providerKeeper.GetConsumerPhase(ctx, "0")
	require.Equal(t, providertypes.CONSUMER_PHASE_REGISTERED, phase)

	consumerMetadata = providertypes.ConsumerMetadata{
		Name:        "chain name",
		Description: "description2",
	}
	response, err = msgServer.CreateConsumer(ctx,
		&providertypes.MsgCreateConsumer{
			Submitter: "submitter2", ChainId: "chainId", Metadata: consumerMetadata,
			InitializationParameters: &providertypes.ConsumerInitializationParameters{},
			PowerShapingParameters:   &providertypes.PowerShapingParameters{},
		})
	require.NoError(t, err)
	// assert that the consumer id is different from the previously registered chain
	require.Equal(t, "1", response.ConsumerId)
	actualMetadata, err = providerKeeper.GetConsumerMetadata(ctx, "1")
	require.NoError(t, err)
	require.Equal(t, consumerMetadata, actualMetadata)
	ownerAddress, err = providerKeeper.GetConsumerOwnerAddress(ctx, "1")
	require.NoError(t, err)
	require.Equal(t, "submitter2", ownerAddress)
	phase = providerKeeper.GetConsumerPhase(ctx, "1")
	require.Equal(t, providertypes.CONSUMER_PHASE_REGISTERED, phase)
}

func TestUpdateConsumer(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	msgServer := providerkeeper.NewMsgServerImpl(&providerKeeper)

	// try to update a non-existing (i.e., no consumer id exists)
	_, err := msgServer.UpdateConsumer(ctx,
		&providertypes.MsgUpdateConsumer{
			Owner: "owner", ConsumerId: "0", NewOwnerAddress: "cosmos1dkas8mu4kyhl5jrh4nzvm65qz588hy9qcz08la",
			Metadata:                 nil,
			InitializationParameters: nil,
			PowerShapingParameters:   nil,
		})
	require.Error(t, err, "cannot update consumer chain")

	// create a chain before updating it
	createConsumerResponse, err := msgServer.CreateConsumer(ctx,
		&providertypes.MsgCreateConsumer{
			Submitter: "submitter", ChainId: "chainId",
			Metadata: providertypes.ConsumerMetadata{
				Name:        "name",
				Description: "description",
				Metadata:    "metadata",
			},
			InitializationParameters: nil,
			PowerShapingParameters:   nil,
		})
	require.NoError(t, err)
	consumerId := createConsumerResponse.ConsumerId

	mocks.MockAccountKeeper.EXPECT().AddressCodec().Return(address.NewBech32Codec("cosmos")).AnyTimes()
	_, err = msgServer.UpdateConsumer(ctx,
		&providertypes.MsgUpdateConsumer{
			Owner: "wrong owner", ConsumerId: consumerId, NewOwnerAddress: "cosmos1dkas8mu4kyhl5jrh4nzvm65qz588hy9qcz08la",
			Metadata:                 nil,
			InitializationParameters: nil,
			PowerShapingParameters:   nil,
		})
	require.Error(t, err, "expected owner address")

	expectedConsumerMetadata := providertypes.ConsumerMetadata{
		Name:        "name2",
		Description: "description2",
		Metadata:    "metadata2",
	}

	expectedInitializationParameters := testkeeper.GetTestInitializationParameters()
	expectedPowerShapingParameters := testkeeper.GetTestPowerShapingParameters()

	expectedOwnerAddress := "cosmos1dkas8mu4kyhl5jrh4nzvm65qz588hy9qcz08la"
	_, err = msgServer.UpdateConsumer(ctx,
		&providertypes.MsgUpdateConsumer{
			Owner: "submitter", ConsumerId: consumerId, NewOwnerAddress: expectedOwnerAddress,
			Metadata:                 &expectedConsumerMetadata,
			InitializationParameters: &expectedInitializationParameters,
			PowerShapingParameters:   &expectedPowerShapingParameters,
		})
	require.NoError(t, err)

	// assert that owner address was updated
	ownerAddress, err := providerKeeper.GetConsumerOwnerAddress(ctx, consumerId)
	require.NoError(t, err)
	require.Equal(t, expectedOwnerAddress, ownerAddress)

	// assert that consumer metadata were updated
	actualConsumerMetadata, err := providerKeeper.GetConsumerMetadata(ctx, consumerId)
	require.NoError(t, err)
	require.Equal(t, expectedConsumerMetadata, actualConsumerMetadata)

	// assert that initialization parameters were updated
	actualInitializationParameters, err := providerKeeper.GetConsumerInitializationParameters(ctx, consumerId)
	require.NoError(t, err)
	require.Equal(t, expectedInitializationParameters, actualInitializationParameters)

	// assert that power-shaping parameters were updated
	actualPowerShapingParameters, err := providerKeeper.GetConsumerPowerShapingParameters(ctx, consumerId)
	require.NoError(t, err)
	require.Equal(t, expectedPowerShapingParameters, actualPowerShapingParameters)

	// assert phase
	phase := providerKeeper.GetConsumerPhase(ctx, consumerId)
	require.Equal(t, providertypes.CONSUMER_PHASE_INITIALIZED, phase)

	// assert that chain is set to launch
	consumerIds, err := providerKeeper.GetConsumersToBeLaunched(ctx, expectedInitializationParameters.SpawnTime)
	require.NoError(t, err)
	require.Equal(t, providertypes.ConsumerIds{
		Ids: []string{consumerId},
	}, consumerIds)

	// re-update (change spawnTime) and verify that the chain is still to be launched at the new spawn time
	previousSpawnTime := expectedInitializationParameters.SpawnTime
	updatedSpawnTime := expectedInitializationParameters.SpawnTime.Add(time.Hour)
	expectedInitializationParameters.SpawnTime = updatedSpawnTime
	_, err = msgServer.UpdateConsumer(ctx,
		&providertypes.MsgUpdateConsumer{
			Owner: expectedOwnerAddress, ConsumerId: consumerId,
			Metadata:                 &expectedConsumerMetadata,
			InitializationParameters: &expectedInitializationParameters,
			PowerShapingParameters:   &expectedPowerShapingParameters,
		})
	require.NoError(t, err)

	consumerIds, err = providerKeeper.GetConsumersToBeLaunched(ctx, previousSpawnTime)
	require.NoError(t, err)
	require.Empty(t, consumerIds)

	consumerIds, err = providerKeeper.GetConsumersToBeLaunched(ctx, updatedSpawnTime)
	require.NoError(t, err)
	require.Equal(t, providertypes.ConsumerIds{
		Ids: []string{consumerId},
	}, consumerIds)
}
