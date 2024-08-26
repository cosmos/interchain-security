package keeper_test

import (
	"github.com/cosmos/cosmos-sdk/codec/address"
	testkeeper "github.com/cosmos/interchain-security/v5/testutil/keeper"
	providerkeeper "github.com/cosmos/interchain-security/v5/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	"github.com/stretchr/testify/require"
	"testing"
	"time"
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
		&providertypes.MsgCreateConsumer{Signer: "signer", ChainId: "chainId", Metadata: consumerMetadata,
			InitializationParameters: &providertypes.ConsumerInitializationParameters{},
			PowerShapingParameters:   &providertypes.PowerShapingParameters{}})
	require.NoError(t, err)
	require.Equal(t, "0", response.ConsumerId)
	actualMetadata, err := providerKeeper.GetConsumerMetadata(ctx, "0")
	require.NoError(t, err)
	require.Equal(t, consumerMetadata, actualMetadata)
	ownerAddress, err := providerKeeper.GetConsumerOwnerAddress(ctx, "0")
	require.Equal(t, "signer", ownerAddress)
	phase, found := providerKeeper.GetConsumerPhase(ctx, "0")
	require.True(t, found)
	require.Equal(t, providerkeeper.Registered, phase)

	consumerMetadata = providertypes.ConsumerMetadata{
		Name:        "chain name",
		Description: "description2",
	}
	response, err = msgServer.CreateConsumer(ctx,
		&providertypes.MsgCreateConsumer{Signer: "signer2", ChainId: "chainId", Metadata: consumerMetadata,
			InitializationParameters: &providertypes.ConsumerInitializationParameters{},
			PowerShapingParameters:   &providertypes.PowerShapingParameters{}})
	require.NoError(t, err)
	// assert that the consumer id is different from the previously registered chain
	require.Equal(t, "1", response.ConsumerId)
	actualMetadata, err = providerKeeper.GetConsumerMetadata(ctx, "1")
	require.NoError(t, err)
	require.Equal(t, consumerMetadata, actualMetadata)
	ownerAddress, err = providerKeeper.GetConsumerOwnerAddress(ctx, "1")
	require.Equal(t, "signer2", ownerAddress)
	phase, found = providerKeeper.GetConsumerPhase(ctx, "1")
	require.True(t, found)
	require.Equal(t, providerkeeper.Registered, phase)
}

func TestUpdateConsumer(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	msgServer := providerkeeper.NewMsgServerImpl(&providerKeeper)

	// try to update a non-existing (i.e., no consumer id exists)
	_, err := msgServer.UpdateConsumer(ctx,
		&providertypes.MsgUpdateConsumer{Signer: "signer", ConsumerId: "0", NewOwnerAddress: "cosmos1dkas8mu4kyhl5jrh4nzvm65qz588hy9qcz08la",
			Metadata:                 nil,
			InitializationParameters: nil,
			PowerShapingParameters:   nil,
		})
	require.Error(t, err, "cannot update consumer chain")

	// create a chain before updating it
	createConsumerResponse, err := msgServer.CreateConsumer(ctx,
		&providertypes.MsgCreateConsumer{Signer: "signer", ChainId: "chainId",
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
		&providertypes.MsgUpdateConsumer{Signer: "wrong signer", ConsumerId: consumerId, NewOwnerAddress: "cosmos1dkas8mu4kyhl5jrh4nzvm65qz588hy9qcz08la",
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
		&providertypes.MsgUpdateConsumer{Signer: "signer", ConsumerId: consumerId, NewOwnerAddress: expectedOwnerAddress,
			Metadata:                 &expectedConsumerMetadata,
			InitializationParameters: &expectedInitializationParameters,
			PowerShapingParameters:   &expectedPowerShapingParameters})
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
	phase, found := providerKeeper.GetConsumerPhase(ctx, consumerId)
	require.True(t, found)
	require.Equal(t, providerkeeper.Initialized, phase)

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
		&providertypes.MsgUpdateConsumer{Signer: expectedOwnerAddress, ConsumerId: consumerId,
			Metadata:                 &expectedConsumerMetadata,
			InitializationParameters: &expectedInitializationParameters,
			PowerShapingParameters:   &expectedPowerShapingParameters})
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
