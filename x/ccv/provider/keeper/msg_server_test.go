package keeper_test

import (
	"testing"
	"time"

	"cosmossdk.io/math"
	"github.com/cosmos/ibc-go/v10/modules/core/02-client/types"
	"github.com/golang/mock/gomock"

	"github.com/stretchr/testify/require"

	"github.com/cosmos/cosmos-sdk/codec/address"

	testkeeper "github.com/cosmos/interchain-security/v7/testutil/keeper"
	providerkeeper "github.com/cosmos/interchain-security/v7/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/v7/x/ccv/provider/types"
)

func TestCreateConsumer(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	mocks.MockSlashingKeeper.EXPECT().DowntimeJailDuration(gomock.Any()).Return(time.Second*600, nil).AnyTimes()
	mocks.MockSlashingKeeper.EXPECT().SlashFractionDoubleSign(gomock.Any()).Return(math.LegacyNewDec(0), nil).AnyTimes()

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
	infractionParam, err := providerKeeper.GetInfractionParameters(ctx, response.ConsumerId)
	require.NoError(t, err)
	expectedInfractionParameters, err := providertypes.DefaultConsumerInfractionParameters(ctx, mocks.MockSlashingKeeper)
	require.NoError(t, err)
	require.Equal(t, expectedInfractionParameters, infractionParam)

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

	mocks.MockSlashingKeeper.EXPECT().DowntimeJailDuration(gomock.Any()).Return(time.Second*600, nil).AnyTimes()
	mocks.MockSlashingKeeper.EXPECT().SlashFractionDoubleSign(gomock.Any()).Return(math.LegacyNewDec(0), nil).AnyTimes()
	unbondingTime := 2 * time.Second
	mocks.MockStakingKeeper.EXPECT().UnbondingTime(gomock.Any()).Return(unbondingTime, nil).AnyTimes()

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
	chainId := "chainId-1"
	createConsumerResponse, err := msgServer.CreateConsumer(ctx,
		&providertypes.MsgCreateConsumer{
			Submitter: "submitter", ChainId: chainId,
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

	// assert that we can change the chain id of a registered chain
	expectedChainId := "newChainId-1"
	_, err = msgServer.UpdateConsumer(ctx,
		&providertypes.MsgUpdateConsumer{
			Owner: "submitter", ConsumerId: consumerId,
			Metadata:                 nil,
			InitializationParameters: nil,
			PowerShapingParameters:   nil,
			NewChainId:               expectedChainId,
		})
	require.NoError(t, err)
	chainId, err = providerKeeper.GetConsumerChainId(ctx, consumerId)
	require.NoError(t, err)
	require.Equal(t, expectedChainId, chainId)

	// assert that we cannot change the chain to that of a reserved chain id
	_, err = msgServer.UpdateConsumer(ctx,
		&providertypes.MsgUpdateConsumer{
			Owner: "submitter", ConsumerId: consumerId,
			Metadata:                 nil,
			InitializationParameters: nil,
			PowerShapingParameters:   nil,
			NewChainId:               "stride-1", // reversed chain id
		})
	require.ErrorContains(t, err, "cannot use a reserved chain id")

	expectedConsumerMetadata := providertypes.ConsumerMetadata{
		Name:        "name2",
		Description: "description2",
		Metadata:    "metadata2",
	}

	expectedInitializationParameters := testkeeper.GetTestInitializationParameters()
	expectedInitializationParameters.InitialHeight.RevisionNumber = 1
	expectedPowerShapingParameters := testkeeper.GetTestPowerShapingParameters()
	expectedInfractionParameters := providertypes.InfractionParameters{
		DoubleSign: &providertypes.SlashJailParameters{
			JailDuration:  1000 * time.Second,
			SlashFraction: math.LegacyNewDecWithPrec(4, 1), // 0.4
		},
		Downtime: &providertypes.SlashJailParameters{
			JailDuration:  500 * time.Second,
			SlashFraction: math.LegacyNewDec(0),
		},
	}

	expectedOwnerAddress := "cosmos1dkas8mu4kyhl5jrh4nzvm65qz588hy9qcz08la"
	expectedChainId = "updatedChainId-1"
	_, err = msgServer.UpdateConsumer(ctx,
		&providertypes.MsgUpdateConsumer{
			Owner: "submitter", ConsumerId: consumerId, NewOwnerAddress: expectedOwnerAddress,
			Metadata:                 &expectedConsumerMetadata,
			InitializationParameters: &expectedInitializationParameters,
			PowerShapingParameters:   &expectedPowerShapingParameters,
			InfractionParameters:     &expectedInfractionParameters,
			NewChainId:               expectedChainId,
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

	// assert that infraction parameters were updated
	actualInfractionParameters, err := providerKeeper.GetInfractionParameters(ctx, consumerId)
	require.NoError(t, err)
	require.Equal(t, expectedInfractionParameters, actualInfractionParameters)

	// assert that the chain id has been updated
	actualChainId, err := providerKeeper.GetConsumerChainId(ctx, consumerId)
	require.NoError(t, err)
	require.Equal(t, expectedChainId, actualChainId)

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

	// assert that we CANNOT update the initialization parameters of a launched chain
	providerKeeper.SetConsumerPhase(ctx, consumerId, providertypes.CONSUMER_PHASE_LAUNCHED)
	_, err = msgServer.UpdateConsumer(ctx,
		&providertypes.MsgUpdateConsumer{
			Owner: expectedOwnerAddress, ConsumerId: consumerId,
			Metadata:                 nil,
			InitializationParameters: &expectedInitializationParameters,
			PowerShapingParameters:   nil,
		})
	require.ErrorContains(t, err, "cannot update the initialization parameters of an an already launched chain")

	// assert that we CANNOT change the chain id of a launched chain
	providerKeeper.SetConsumerPhase(ctx, consumerId, providertypes.CONSUMER_PHASE_LAUNCHED)
	_, err = msgServer.UpdateConsumer(ctx,
		&providertypes.MsgUpdateConsumer{
			Owner: expectedOwnerAddress, ConsumerId: consumerId,
			Metadata:                 nil,
			InitializationParameters: nil,
			PowerShapingParameters:   nil,
			NewChainId:               "newChainId",
		})
	require.ErrorContains(t, err, "cannot update chain id of a non-prelaunched chain")

	// assert that we can use the chain's current chain id as `NewChainId` even if the chain has launched
	// as effectively this does not change anything
	chainId, err = providerKeeper.GetConsumerChainId(ctx, consumerId)
	require.NoError(t, err)
	providerKeeper.SetConsumerPhase(ctx, consumerId, providertypes.CONSUMER_PHASE_LAUNCHED)
	_, err = msgServer.UpdateConsumer(ctx,
		&providertypes.MsgUpdateConsumer{
			Owner: expectedOwnerAddress, ConsumerId: consumerId,
			Metadata:                 nil,
			InitializationParameters: nil,
			PowerShapingParameters:   nil,
			NewChainId:               chainId,
		})
	require.NoError(t, err)

	// assert that we can update the consumer metadata of a launched chain
	providerKeeper.SetConsumerPhase(ctx, consumerId, providertypes.CONSUMER_PHASE_LAUNCHED)
	expectedConsumerMetadata.Name = "name of a launched chain"
	_, err = msgServer.UpdateConsumer(ctx,
		&providertypes.MsgUpdateConsumer{
			Owner: expectedOwnerAddress, ConsumerId: consumerId,
			Metadata:                 &expectedConsumerMetadata,
			InitializationParameters: nil,
			PowerShapingParameters:   nil,
		})
	require.NoError(t, err)
	actualConsumerMetadata, err = providerKeeper.GetConsumerMetadata(ctx, consumerId)
	require.NoError(t, err)
	require.Equal(t, expectedConsumerMetadata, actualConsumerMetadata)

	// assert that we can update the power-shaping parameters of a launched chain
	providerKeeper.SetConsumerPhase(ctx, consumerId, providertypes.CONSUMER_PHASE_LAUNCHED)
	expectedPowerShapingParameters.ValidatorSetCap = 123
	_, err = msgServer.UpdateConsumer(ctx,
		&providertypes.MsgUpdateConsumer{
			Owner: expectedOwnerAddress, ConsumerId: consumerId,
			Metadata:                 nil,
			InitializationParameters: nil,
			PowerShapingParameters:   &expectedPowerShapingParameters,
		})
	require.NoError(t, err)
	actualPowerShapingParameters, err = providerKeeper.GetConsumerPowerShapingParameters(ctx, consumerId)
	require.NoError(t, err)
	require.Equal(t, expectedPowerShapingParameters, actualPowerShapingParameters)

	// assert that we can update the infraction parameters of a launched chain
	providerKeeper.SetConsumerPhase(ctx, consumerId, providertypes.CONSUMER_PHASE_LAUNCHED)
	newExpectedInfractionParameters := providertypes.InfractionParameters{
		DoubleSign: &providertypes.SlashJailParameters{
			JailDuration:  2000 * time.Second,
			SlashFraction: math.LegacyNewDecWithPrec(6, 1), // 0.6
		},
		Downtime: &providertypes.SlashJailParameters{
			JailDuration:  1000 * time.Second,
			SlashFraction: math.LegacyNewDecWithPrec(2, 1),
		},
	}
	_, err = msgServer.UpdateConsumer(ctx,
		&providertypes.MsgUpdateConsumer{
			Owner: expectedOwnerAddress, ConsumerId: consumerId,
			Metadata:                 nil,
			InitializationParameters: nil,
			PowerShapingParameters:   nil,
			InfractionParameters:     &newExpectedInfractionParameters,
		})
	require.NoError(t, err)
	// infraction parameters are queued and not updated yet to newExpectedInfractionParameters since the chain is launched
	require.Equal(t, expectedInfractionParameters, actualInfractionParameters)
	// trigger update of queud infraction params after unbonding time is passed
	providerKeeper.BeginBlockUpdateInfractionParameters(ctx.WithBlockTime(ctx.BlockTime().Add(2 * unbondingTime)))
	actualInfractionParameters, err = providerKeeper.GetInfractionParameters(ctx, consumerId)
	require.NoError(t, err)
	require.Equal(t, newExpectedInfractionParameters, actualInfractionParameters)

	// assert that if we call `MsgUpdateConsumer` with a spawn time of zero on an initialized chain, the chain
	// will not be scheduled to launch and will move back to its Registered phase
	providerKeeper.SetConsumerPhase(ctx, consumerId, providertypes.CONSUMER_PHASE_INITIALIZED)
	// first assert that the chain is scheduled to launch
	previousSpawnTime = expectedInitializationParameters.SpawnTime
	consumerIds, err = providerKeeper.GetConsumersToBeLaunched(ctx, previousSpawnTime)
	require.NoError(t, err)
	require.Equal(t, providertypes.ConsumerIds{
		Ids: []string{consumerId},
	}, consumerIds)

	// then, update with a spawn time of zero to prevent the chain from launching
	expectedInitializationParameters.SpawnTime = time.Time{}
	// also update an arbitrary field of the initialization parameters
	// to verify that the parameters of the chain get updated
	expectedInitializationParameters.InitialHeight = types.NewHeight(1, 123456)
	_, err = msgServer.UpdateConsumer(ctx,
		&providertypes.MsgUpdateConsumer{
			Owner: expectedOwnerAddress, ConsumerId: consumerId,
			Metadata:                 nil,
			InitializationParameters: &expectedInitializationParameters,
			PowerShapingParameters:   nil,
		})
	require.NoError(t, err)
	// assert the chain is not scheduled to launch
	consumerIds, err = providerKeeper.GetConsumersToBeLaunched(ctx, previousSpawnTime)
	require.NoError(t, err)
	require.Empty(t, consumerIds)
	// also assert that no chain is scheduled to launch at zero time
	consumerIds, err = providerKeeper.GetConsumersToBeLaunched(ctx, time.Time{})
	require.NoError(t, err)
	require.Empty(t, consumerIds)
	// assert that the chain has moved to the registered phase because it is not ready to launch
	phase = providerKeeper.GetConsumerPhase(ctx, consumerId)
	require.Equal(t, providertypes.CONSUMER_PHASE_REGISTERED, phase)
	// assert that the initialization parameters of the chain were nevertheless updated
	actualInitializationParameters, err = providerKeeper.GetConsumerInitializationParameters(ctx, consumerId)
	require.NoError(t, err)
	require.Equal(t, expectedInitializationParameters, actualInitializationParameters)
}
