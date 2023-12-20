package keeper_test

import (
	"testing"

	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"
	"github.com/stretchr/testify/require"

	testutil "github.com/cosmos/interchain-security/v3/testutil/keeper"

	"github.com/cosmos/interchain-security/v3/x/ccv/consumer/keeper"
	"github.com/cosmos/interchain-security/v3/x/ccv/consumer/types"
	ccvtypes "github.com/cosmos/interchain-security/v3/x/ccv/types"
)

func TestMigrateConsumerPacketData(t *testing.T) {
	consumerKeeper, ctx, ctrl, _ := testutil.GetConsumerKeeperAndCtx(t, testutil.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// Set some pending data packets in the old format
	packets := types.ConsumerPacketDataList{
		List: []ccvtypes.ConsumerPacketData{
			{
				Type: ccvtypes.SlashPacket,
				Data: &ccvtypes.ConsumerPacketData_SlashPacketData{
					SlashPacketData: &ccvtypes.SlashPacketData{
						ValsetUpdateId: 77,
					},
				},
			},
			{
				Type: ccvtypes.VscMaturedPacket,
				Data: &ccvtypes.ConsumerPacketData_VscMaturedPacketData{
					VscMaturedPacketData: &ccvtypes.VSCMaturedPacketData{
						ValsetUpdateId: 88,
					},
				},
			},
			{
				Type: ccvtypes.VscMaturedPacket,
				Data: &ccvtypes.ConsumerPacketData_VscMaturedPacketData{
					VscMaturedPacketData: &ccvtypes.VSCMaturedPacketData{
						ValsetUpdateId: 99,
					},
				},
			},
		},
	}

	// Set old data
	consumerKeeper.SetPendingPacketsOnlyForTesting(ctx, packets)

	// Migrate
	consumerKeeper.MigrateConsumerPacketData(ctx)

	// Check that the data is migrated properly
	obtainedPackets := consumerKeeper.GetPendingPackets(ctx)
	require.Len(t, packets.List, 3)

	require.Equal(t, ccvtypes.SlashPacket, obtainedPackets[0].Type)
	require.Equal(t, ccvtypes.VscMaturedPacket, obtainedPackets[1].Type)
	require.Equal(t, ccvtypes.VscMaturedPacket, obtainedPackets[2].Type)

	require.Equal(t, uint64(77), obtainedPackets[0].GetSlashPacketData().ValsetUpdateId)
	require.Equal(t, uint64(88), obtainedPackets[1].GetVscMaturedPacketData().ValsetUpdateId)
	require.Equal(t, uint64(99), obtainedPackets[2].GetVscMaturedPacketData().ValsetUpdateId)
}

func TestMigrateParams(t *testing.T) {
	params := testutil.NewInMemKeeperParams(t)
	consumerKeeper, ctx, ctrl, _ := testutil.GetConsumerKeeperAndCtx(t, params)
	defer ctrl.Finish()

	testCases := []struct {
		name          string
		legacyParams  func() paramtypes.Subspace
		expetedParams ccvtypes.ConsumerParams
	}{
		{
			"default params",
			func() paramtypes.Subspace {
				subspace := params.ParamsSubspace
				defaultParams := ccvtypes.DefaultParams()
				subspace.SetParamSet(ctx, &defaultParams)
				return *subspace
			},
			ccvtypes.DefaultParams(),
		},
	}
	for _, tc := range testCases {
		migrator := keeper.NewMigrator(consumerKeeper, tc.legacyParams())
		err := migrator.MigrateParams(ctx)
		require.NoError(t, err)
		params := consumerKeeper.GetConsumerParams(ctx)
		require.Equal(t, tc.expetedParams, params)
	}
}
