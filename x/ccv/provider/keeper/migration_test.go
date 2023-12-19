package keeper_test

import (
	"testing"
	"time"

	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"
	testutil "github.com/cosmos/interchain-security/v3/testutil/keeper"
	"github.com/cosmos/interchain-security/v3/x/ccv/provider/keeper"
	"github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
	"github.com/stretchr/testify/require"
)

func TestMigrateParams(t *testing.T) {
	params := testutil.NewInMemKeeperParams(t)
	providerKeeper, ctx, ctrl, _ := testutil.GetProviderKeeperAndCtx(t, params)
	defer ctrl.Finish()

	testCases := []struct {
		name          string
		legacyParams  func() paramtypes.Subspace
		expetedParams types.Params
	}{
		{
			"default params",
			func() paramtypes.Subspace {
				subspace := params.ParamsSubspace
				defaultParams := types.DefaultParams()
				subspace.SetParamSet(ctx, &defaultParams)
				return *subspace
			},
			types.DefaultParams(),
		},
	}
	for _, tc := range testCases {
		migrator := keeper.NewMigrator(providerKeeper, tc.legacyParams())
		err := migrator.MigrateParams(ctx)
		require.NoError(t, err)
		params := providerKeeper.GetParams(ctx)
		require.Equal(t, tc.expetedParams, params)
	}
}

func TestMigrate2To3(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testutil.GetProviderKeeperAndCtx(t, testutil.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// Set consumer client ids to mock consumers being connected to provider
	providerKeeper.SetConsumerClientId(ctx, "chain-1", "client-1")
	providerKeeper.SetConsumerClientId(ctx, "chain-2", "client-2")
	providerKeeper.SetConsumerClientId(ctx, "chain-3", "client-3")

	// Queue some data for chain-1
	providerKeeper.QueueThrottledPacketDataOnlyForTesting(
		ctx, "chain-1", 66, testutil.GetNewSlashPacketData())
	providerKeeper.QueueThrottledPacketDataOnlyForTesting(
		ctx, "chain-1", 67, testutil.GetNewVSCMaturedPacketData())
	providerKeeper.QueueThrottledPacketDataOnlyForTesting(
		ctx, "chain-1", 68, testutil.GetNewSlashPacketData())
	providerKeeper.QueueThrottledPacketDataOnlyForTesting(
		ctx, "chain-1", 69, testutil.GetNewVSCMaturedPacketData())

	// Queue some data for chain-2
	providerKeeper.QueueThrottledPacketDataOnlyForTesting(
		ctx, "chain-2", 789, testutil.GetNewVSCMaturedPacketData())
	providerKeeper.QueueThrottledPacketDataOnlyForTesting(
		ctx, "chain-2", 790, testutil.GetNewSlashPacketData())
	providerKeeper.QueueThrottledPacketDataOnlyForTesting(
		ctx, "chain-2", 791, testutil.GetNewVSCMaturedPacketData())

	// Queue some data for chain-3
	providerKeeper.QueueThrottledPacketDataOnlyForTesting(
		ctx, "chain-3", 123, testutil.GetNewSlashPacketData())
	providerKeeper.QueueThrottledPacketDataOnlyForTesting(
		ctx, "chain-3", 124, testutil.GetNewVSCMaturedPacketData())
	providerKeeper.QueueThrottledPacketDataOnlyForTesting(
		ctx, "chain-3", 125, testutil.GetNewVSCMaturedPacketData())

	// Confirm getter methods return expected values
	slash1, vscm1 := providerKeeper.GetAllThrottledPacketData(ctx, "chain-1")
	require.Len(t, slash1, 2)
	require.Len(t, vscm1, 2)

	slash2, vscm2 := providerKeeper.GetAllThrottledPacketData(ctx, "chain-2")
	require.Len(t, slash2, 1)
	require.Len(t, vscm2, 2)

	slash3, vscm3 := providerKeeper.GetAllThrottledPacketData(ctx, "chain-3")
	require.Len(t, slash3, 1)
	require.Len(t, vscm3, 2)

	// Set vsc send timestamp for every queued vsc matured packet,
	// as a way to assert that the vsc matured packets are handled in the migration.
	//
	// That is, timestamp should exist before a vsc matured packet is handled,
	// and deleted after handling.
	for _, data := range vscm1 {
		providerKeeper.SetVscSendTimestamp(ctx, "chain-1", data.ValsetUpdateId, time.Now())
	}
	for _, data := range vscm2 {
		providerKeeper.SetVscSendTimestamp(ctx, "chain-2", data.ValsetUpdateId, time.Now())
	}
	for _, data := range vscm3 {
		providerKeeper.SetVscSendTimestamp(ctx, "chain-3", data.ValsetUpdateId, time.Now())
	}

	// Confirm timestamps are set
	for _, data := range vscm1 {
		_, found := providerKeeper.GetVscSendTimestamp(ctx, "chain-1", data.ValsetUpdateId)
		require.True(t, found)
	}
	for _, data := range vscm2 {
		_, found := providerKeeper.GetVscSendTimestamp(ctx, "chain-2", data.ValsetUpdateId)
		require.True(t, found)
	}
	for _, data := range vscm3 {
		_, found := providerKeeper.GetVscSendTimestamp(ctx, "chain-3", data.ValsetUpdateId)
		require.True(t, found)
	}

	// Run migration
	err := providerKeeper.MigrateQueuedPackets(ctx)
	require.NoError(t, err)

	// Confirm throttled data is now deleted
	slash1, vscm1 = providerKeeper.GetAllThrottledPacketData(ctx, "chain-1")
	require.Empty(t, slash1)
	require.Empty(t, vscm1)
	slash2, vscm2 = providerKeeper.GetAllThrottledPacketData(ctx, "chain-2")
	require.Empty(t, slash2)
	require.Empty(t, vscm2)
	slash3, vscm3 = providerKeeper.GetAllThrottledPacketData(ctx, "chain-3")
	require.Empty(t, slash3)
	require.Empty(t, vscm3)

	// Confirm timestamps are deleted, meaning vsc matured packets were handled
	for _, data := range vscm1 {
		_, found := providerKeeper.GetVscSendTimestamp(ctx, "chain-1", data.ValsetUpdateId)
		require.False(t, found)
	}
	for _, data := range vscm2 {
		_, found := providerKeeper.GetVscSendTimestamp(ctx, "chain-2", data.ValsetUpdateId)
		require.False(t, found)
	}
	for _, data := range vscm3 {
		_, found := providerKeeper.GetVscSendTimestamp(ctx, "chain-3", data.ValsetUpdateId)
		require.False(t, found)
	}
}
