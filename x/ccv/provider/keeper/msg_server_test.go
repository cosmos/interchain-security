package keeper_test

import (
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
