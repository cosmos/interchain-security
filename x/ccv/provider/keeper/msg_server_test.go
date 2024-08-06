package keeper_test

import (
	"github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
	testkeeper "github.com/cosmos/interchain-security/v5/testutil/keeper"
	providerkeeper "github.com/cosmos/interchain-security/v5/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	"github.com/stretchr/testify/require"
	"testing"
	"time"
)

func TestRegisterConsumer(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	msgServer := providerkeeper.NewMsgServerImpl(&providerKeeper)

	expectedRecord := providertypes.ConsumerRegistrationRecord{
		Title:       "title",
		Description: "description",
		ChainId:     "chain_id",
	}
	response, err := msgServer.RegisterConsumer(ctx,
		&providertypes.MsgRegisterConsumer{Signer: "signer", RegistrationRecord: &expectedRecord})
	require.NoError(t, err)
	require.Equal(t, "0", response.ConsumerId)
	actualRecord, found := providerKeeper.GetConsumerIdToRegistrationRecord(ctx, "0")
	require.True(t, found)
	require.Equal(t, expectedRecord, actualRecord)
	ownerAddress, found := providerKeeper.GetConsumerIdToOwnerAddress(ctx, "0")
	require.Equal(t, "signer", ownerAddress)
	phase, found := providerKeeper.GetConsumerIdToPhase(ctx, "0")
	require.True(t, found)
	require.Equal(t, providerkeeper.Registered, phase)

	expectedRecord = providertypes.ConsumerRegistrationRecord{
		Title:       "title2",
		Description: "description2",
		ChainId:     "chain_id2",
	}
	response, err = msgServer.RegisterConsumer(ctx,
		&providertypes.MsgRegisterConsumer{Signer: "signer2", RegistrationRecord: &expectedRecord})
	require.NoError(t, err)
	// assert that the consumer id is different from the previously registered chain
	require.Equal(t, "1", response.ConsumerId)
	actualRecord, found = providerKeeper.GetConsumerIdToRegistrationRecord(ctx, "1")
	require.True(t, found)
	require.Equal(t, expectedRecord, actualRecord)
	ownerAddress, found = providerKeeper.GetConsumerIdToOwnerAddress(ctx, "1")
	require.Equal(t, "signer2", ownerAddress)
	phase, found = providerKeeper.GetConsumerIdToPhase(ctx, "1")
	require.True(t, found)
	require.Equal(t, providerkeeper.Registered, phase)

}

func TestInitializeConsumer(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	msgServer := providerkeeper.NewMsgServerImpl(&providerKeeper)

	// initializing a chain with no phase, or a chain that is launched or stopped should give an error
	_, err := msgServer.InitializeConsumer(ctx,
		&providertypes.MsgInitializeConsumer{
			Authority:            "signer",
			ConsumerId:           "0",
			InitializationRecord: &providertypes.ConsumerInitializationRecord{}})
	require.ErrorContains(t, err, "its registered or initialized phase")

	providerKeeper.SetConsumerIdToPhase(ctx, "0", providerkeeper.Launched)
	_, err = msgServer.InitializeConsumer(ctx,
		&providertypes.MsgInitializeConsumer{
			Authority:            "signer",
			ConsumerId:           "0",
			InitializationRecord: &providertypes.ConsumerInitializationRecord{}})
	require.ErrorContains(t, err, "its registered or initialized phase")

	providerKeeper.SetConsumerIdToPhase(ctx, "0", providerkeeper.Stopped)
	_, err = msgServer.InitializeConsumer(ctx,
		&providertypes.MsgInitializeConsumer{
			Authority:            "signer",
			ConsumerId:           "0",
			InitializationRecord: &providertypes.ConsumerInitializationRecord{}})
	require.ErrorContains(t, err, "its registered or initialized phase")

	// register chains with consumers ids "0" and "1"
	_, _ = msgServer.RegisterConsumer(ctx,
		&providertypes.MsgRegisterConsumer{
			Signer:             "signer",
			RegistrationRecord: &providertypes.ConsumerRegistrationRecord{}})

	_, _ = msgServer.RegisterConsumer(ctx,
		&providertypes.MsgRegisterConsumer{
			Signer:             "signer2",
			RegistrationRecord: &providertypes.ConsumerRegistrationRecord{}})

	// assert that you CANNOT initialize a consumer chain that you do NOT own
	_, err = msgServer.InitializeConsumer(ctx,
		&providertypes.MsgInitializeConsumer{
			Authority:            "signer2",
			ConsumerId:           "0",
			InitializationRecord: &providertypes.ConsumerInitializationRecord{}})
	require.ErrorContains(t, err, "expected owner")

	// initialize chain with consumer id "0"
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

	_, err = msgServer.InitializeConsumer(ctx,
		&providertypes.MsgInitializeConsumer{
			Authority:            "signer",
			ConsumerId:           "0",
			InitializationRecord: &expectedRecord})
	require.NoError(t, err)
	actualRecord, found := providerKeeper.GetConsumerIdToInitializationRecord(ctx, "0")
	require.True(t, found)
	require.Equal(t, expectedRecord, actualRecord)
	// verify that the owner of the consumer chain did NOT change
	ownerAddress, found := providerKeeper.GetConsumerIdToOwnerAddress(ctx, "0")
	require.True(t, found)
	require.Equal(t, "signer", ownerAddress)

	// assert that we can re-initialize chain with consumer id "0"
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

	_, err = msgServer.InitializeConsumer(ctx,
		&providertypes.MsgInitializeConsumer{
			Authority:            "signer",
			ConsumerId:           "0",
			InitializationRecord: &expectedRecord})
	require.NoError(t, err)
	actualRecord, found = providerKeeper.GetConsumerIdToInitializationRecord(ctx, "0")
	require.True(t, found)
	require.Equal(t, expectedRecord, actualRecord)
	// verify that the owner of the consumer chain did NOT change
	ownerAddress, found = providerKeeper.GetConsumerIdToOwnerAddress(ctx, "0")
	require.True(t, found)
	require.Equal(t, "signer", ownerAddress)

	// initialize chain with consumer id "1" but with a different owner (as part of a governance proposal)

	// first verify that the current owner can initialize the chain
	_, err = msgServer.InitializeConsumer(ctx,
		&providertypes.MsgInitializeConsumer{
			Authority:            "signer2",
			ConsumerId:           "1",
			InitializationRecord: &expectedRecord})
	require.NoError(t, err)
	actualRecord, found = providerKeeper.GetConsumerIdToInitializationRecord(ctx, "1")
	require.True(t, found)
	require.Equal(t, expectedRecord, actualRecord)
	// verify that the owner of the consumer chain did NOT change
	ownerAddress, found = providerKeeper.GetConsumerIdToOwnerAddress(ctx, "1")
	require.True(t, found)
	require.Equal(t, "signer2", ownerAddress)

	// second, reinitialize by with a gov proposal owner
	_, err = msgServer.InitializeConsumer(ctx,
		&providertypes.MsgInitializeConsumer{
			Authority:            providerKeeper.GetAuthority(),
			ConsumerId:           "1",
			InitializationRecord: &expectedRecord})
	require.NoError(t, err)
	actualRecord, found = providerKeeper.GetConsumerIdToInitializationRecord(ctx, "1")
	require.True(t, found)
	require.Equal(t, expectedRecord, actualRecord)
	// verify that the owner of the consumer chain did change
	ownerAddress, found = providerKeeper.GetConsumerIdToOwnerAddress(ctx, "1")
	require.True(t, found)
	require.Equal(t, providerKeeper.GetAuthority(), ownerAddress)
}
