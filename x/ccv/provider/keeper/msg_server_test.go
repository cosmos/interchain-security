package keeper_test

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	testkeeper "github.com/cosmos/interchain-security/v5/testutil/keeper"
	providerkeeper "github.com/cosmos/interchain-security/v5/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	"github.com/stretchr/testify/require"
	"testing"
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
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerId := "0"

	// set up a consumer client, so it seems that chain is running
	providerKeeper.SetConsumerClientId(ctx, consumerId, "clientID")

	// set PSS-related fields to update them later on
	providerKeeper.SetConsumerPowerShapingParameters(ctx, consumer, providertypes.PowerShapingParameters{
		Top_N:              50,
		ValidatorSetCap:    10,
		ValidatorsPowerCap: 34,
		MinStake:           100,
		AllowInactiveVals:  true,
	})
	providerKeeper.SetAllowlist(ctx, consumerId, providertypes.NewProviderConsAddress([]byte("allowlistedAddr1")))
	providerKeeper.SetAllowlist(ctx, consumerId, providertypes.NewProviderConsAddress([]byte("allowlistedAddr2")))
	providerKeeper.SetDenylist(ctx, consumerId, providertypes.NewProviderConsAddress([]byte("denylistedAddr1")))

	expectedTopN := uint32(75)
	expectedValidatorsPowerCap := uint32(67)
	expectedValidatorSetCap := uint32(20)
	expectedAllowlistedValidator := "cosmosvalcons1wpex7anfv3jhystyv3eq20r35a"
	expectedDenylistedValidator := "cosmosvalcons1nx7n5uh0ztxsynn4sje6eyq2ud6rc6klc96w39"
	expectedMinStake := uint64(0)
	expectedAllowInactiveValidators := false

	powerShapingParameters := providertypes.PowerShapingParameters{
		Top_N:              expectedTopN,
		ValidatorsPowerCap: expectedValidatorsPowerCap,
		ValidatorSetCap:    expectedValidatorSetCap,
		Allowlist:          []string{expectedAllowlistedValidator},
		Denylist:           []string{expectedDenylistedValidator},
		MinStake:           expectedMinStake,
		AllowInactiveVals:  expectedAllowInactiveValidators,
	}

	providerKeeper.SetConsumerPhase(ctx, consumerId, providerkeeper.Initialized)
	providerKeeper.SetConsumerPowerShapingParameters(ctx, consumerId, powerShapingParameters)
	err := providerKeeper.UpdateConsumer(ctx, consumerId)
	require.NoError(t, err)

	actualTopN := providerKeeper.GetTopN(ctx, consumerId)
	require.Equal(t, expectedTopN, actualTopN)
	actualValidatorsPowerCap := providerKeeper.GetValidatorsPowerCap(ctx, consumerId)
	require.Equal(t, expectedValidatorsPowerCap, actualValidatorsPowerCap)
	actualValidatorSetCap := providerKeeper.GetValidatorSetCap(ctx, consumerId)
	require.Equal(t, expectedValidatorSetCap, actualValidatorSetCap)

	allowlistedValidator, err := sdk.ConsAddressFromBech32(expectedAllowlistedValidator)
	require.NoError(t, err)
	require.Equal(t, 1, len(providerKeeper.GetAllowList(ctx, consumerId)))
	require.Equal(t, providertypes.NewProviderConsAddress(allowlistedValidator), providerKeeper.GetAllowList(ctx, consumerId)[0])

	denylistedValidator, err := sdk.ConsAddressFromBech32(expectedDenylistedValidator)
	require.NoError(t, err)
	require.Equal(t, 1, len(providerKeeper.GetDenyList(ctx, consumerId)))
	require.Equal(t, providertypes.NewProviderConsAddress(denylistedValidator), providerKeeper.GetDenyList(ctx, consumerId)[0])

	actualMinStake := providerKeeper.GetMinStake(ctx, consumerId)
	require.Equal(t, expectedMinStake, actualMinStake)

	actualAllowInactiveValidators := providerKeeper.AllowsInactiveValidators(ctx, consumerId)
	require.Equal(t, expectedAllowInactiveValidators, actualAllowInactiveValidators)
}
