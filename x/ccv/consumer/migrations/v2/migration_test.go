package v2_test

import (
	"fmt"
	"testing"

	"github.com/stretchr/testify/require"

	storetypes "cosmossdk.io/store/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	testutil "github.com/cosmos/interchain-security/v5/testutil/keeper"
	v2 "github.com/cosmos/interchain-security/v5/x/ccv/consumer/migrations/v2"
	consumertypes "github.com/cosmos/interchain-security/v5/x/ccv/consumer/types"
	ccvtypes "github.com/cosmos/interchain-security/v5/x/ccv/types"
)

func TestMigrateConsumerPacketData(t *testing.T) {
	testingParams := testutil.NewInMemKeeperParams(t)
	consumerKeeper, ctx, ctrl, _ := testutil.GetConsumerKeeperAndCtx(t, testingParams)
	testStore := ctx.KVStore(testingParams.StoreKey)

	defer ctrl.Finish()

	// Set some pending data packets in the old format
	packets := consumertypes.ConsumerPacketDataList{
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

	// assert that new storage is empty
	storedPackets := consumerKeeper.GetPendingPackets(ctx)
	require.Len(t, storedPackets, 0)

	// Set old data
	setPendingPackets(ctx, testStore, packets)
	// GetPendingPackets should panic because the marshalling is different before migration
	require.Panics(t, func() { consumerKeeper.GetPendingPackets(ctx) })

	// Migrate
	v2.MigrateConsumerPacketData(ctx, testStore)

	// Check that the data is migrated properly
	obtainedPackets := consumerKeeper.GetPendingPackets(ctx)
	require.Len(t, obtainedPackets, 3)

	require.Equal(t, ccvtypes.SlashPacket, obtainedPackets[0].Type)
	require.Equal(t, ccvtypes.VscMaturedPacket, obtainedPackets[1].Type)
	require.Equal(t, ccvtypes.VscMaturedPacket, obtainedPackets[2].Type)

	require.Equal(t, uint64(77), obtainedPackets[0].GetSlashPacketData().ValsetUpdateId)
	require.Equal(t, uint64(88), obtainedPackets[1].GetVscMaturedPacketData().ValsetUpdateId)
	require.Equal(t, uint64(99), obtainedPackets[2].GetVscMaturedPacketData().ValsetUpdateId)
}

func setPendingPackets(ctx sdk.Context, store storetypes.KVStore, packets consumertypes.ConsumerPacketDataList) {
	bz, err := packets.Marshal()
	if err != nil {
		panic(fmt.Errorf("failed to marshal ConsumerPacketDataList: %w", err))
	}
	store.Set([]byte{consumertypes.PendingDataPacketsBytePrefix}, bz)
}
