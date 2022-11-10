package keeper_test

import (
	"testing"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	exported "github.com/cosmos/ibc-go/v3/modules/core/exported"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	"github.com/cosmos/interchain-security/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	"github.com/stretchr/testify/require"
)

// TestOnRecvVSCMaturedPacket tests the OnRecvVSCMaturedPacket method of the keeper.
// Particularly the behavior that VSC matured packet data should be handled immediately
// if the pending packet data queue is empty, and should be queued otherwise.
//
// Note: Handling logic itself is not testing in here, just queueing behavior.
func TestOnRecvVSCMaturedPacket(t *testing.T) {

	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()
	providerKeeper.SetParams(ctx, providertypes.DefaultParams())

	// Set channel to chain (faking multiple established channels)
	providerKeeper.SetChannelToChain(ctx, "channel-1", "chain-1")
	providerKeeper.SetChannelToChain(ctx, "channel-2", "chain-2")

	// Execute on recv for chain-1
	ack := executeOnRecvVSCMaturedPacket(t, &providerKeeper, ctx, "channel-1", 1)
	require.Equal(t, channeltypes.NewResultAcknowledgement([]byte{byte(1)}), ack)

	// Assert that the packet data was handled immediately, not queued
	require.Equal(t, uint64(0), providerKeeper.GetPendingPacketDataSize(ctx, "chain-1"))

	// Other queue still empty
	require.Equal(t, uint64(0), providerKeeper.GetPendingPacketDataSize(ctx, "chain-2"))

	// Now queue a slash packet data instance for chain-2, then confirm the on recv method
	// queues the vsc matured behind the slash packet data
	queuePendingPacketData(ctx, &providerKeeper, "chain-2", 1, testkeeper.GetNewSlashPacketData())
	ack = executeOnRecvVSCMaturedPacket(t, &providerKeeper, ctx, "channel-2", 2)
	require.Equal(t, channeltypes.NewResultAcknowledgement([]byte{byte(1)}), ack)
	require.Equal(t, uint64(2), providerKeeper.GetPendingPacketDataSize(ctx, "chain-2"))

	// Other queue still empty
	require.Equal(t, uint64(0), providerKeeper.GetPendingPacketDataSize(ctx, "chain-1"))

	// Receive 5 more vsc matured packets for chain-2, then confirm chain-2 queue size is 7, chain-1 still 0
	for i := 0; i < 5; i++ {
		ack = executeOnRecvVSCMaturedPacket(t, &providerKeeper, ctx, "channel-2", uint64(i+3))
		require.Equal(t, channeltypes.NewResultAcknowledgement([]byte{byte(1)}), ack)
	}
	require.Equal(t, uint64(7), providerKeeper.GetPendingPacketDataSize(ctx, "chain-2"))
	require.Equal(t, uint64(0), providerKeeper.GetPendingPacketDataSize(ctx, "chain-1"))

	// Delete chain-2's data from its queue, then confirm the queue size is 0
	providerKeeper.DeletePendingPacketData(ctx, "chain-2", []uint64{1, 2, 3, 4, 5, 6, 7}...)
	require.Equal(t, uint64(0), providerKeeper.GetPendingPacketDataSize(ctx, "chain-2"))

	// Finally, confirm vsc packet data will again be handled immediately
	ack = executeOnRecvVSCMaturedPacket(t, &providerKeeper, ctx, "channel-2", 8)
	require.Equal(t, channeltypes.NewResultAcknowledgement([]byte{byte(1)}), ack)
	require.Equal(t, uint64(0), providerKeeper.GetPendingPacketDataSize(ctx, "chain-2"))
	require.Equal(t, uint64(0), providerKeeper.GetPendingPacketDataSize(ctx, "chain-1"))
}

// TestOnRecvSlashPacket tests the OnRecvSlashPacket method, and how it interacts with the
// parent and per-chain slash packet queues.
func TestOnRecvSlashPacket(t *testing.T) {

	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()
	providerKeeper.SetParams(ctx, providertypes.DefaultParams())

	// Set channel to chain (faking multiple established channels)
	providerKeeper.SetChannelToChain(ctx, "channel-1", "chain-1")
	providerKeeper.SetChannelToChain(ctx, "channel-2", "chain-2")

	// Receive a slash packet for chain-1 at time.Now()
	ctx = ctx.WithBlockTime(time.Now())
	ack := executeOnRecvSlashPacket(t, &providerKeeper, ctx, "channel-1", 1)
	require.Equal(t, channeltypes.NewResultAcknowledgement([]byte{byte(1)}), ack)

	// Confirm an entry was added to the parent queue, and pending packet data was added to the per-chain queue
	packetEntries := providerKeeper.GetAllPendingSlashPacketEntries(ctx) // parent queue
	require.Equal(t, 1, len(packetEntries))
	require.Equal(t, "chain-1", packetEntries[0].ConsumerChainID)
	require.Equal(t, uint64(1), providerKeeper.GetPendingPacketDataSize(ctx, "chain-1")) // per chain queue

	// Receive a slash packet for chain-2 at time.Now(Add(1 *time.Hour))
	ctx = ctx.WithBlockTime(time.Now().Add(1 * time.Hour))
	ack = executeOnRecvSlashPacket(t, &providerKeeper, ctx, "channel-2", 2)
	require.Equal(t, channeltypes.NewResultAcknowledgement([]byte{byte(1)}), ack)

	// Confirm sizes of parent queue and both per-chain queues
	packetEntries = providerKeeper.GetAllPendingSlashPacketEntries(ctx) // parent queue
	require.Equal(t, 2, len(packetEntries))
	require.Equal(t, "chain-1", packetEntries[0].ConsumerChainID)
	require.Equal(t, "chain-2", packetEntries[1].ConsumerChainID)
	require.Equal(t, uint64(1), providerKeeper.GetPendingPacketDataSize(ctx, "chain-1")) // per chain queue
	require.Equal(t, uint64(1), providerKeeper.GetPendingPacketDataSize(ctx, "chain-2")) // per chain queue
}

func executeOnRecvVSCMaturedPacket(t *testing.T, providerKeeper *keeper.Keeper, ctx sdk.Context,
	channelID string, ibcSeqNum uint64) exported.Acknowledgement {

	// Instantiate vsc matured packet data and bytes
	data := testkeeper.GetNewVSCMaturedPacketData()
	dataBz, err := data.Marshal()
	require.NoError(t, err)

	return providerKeeper.OnRecvVSCMaturedPacket(
		ctx,
		channeltypes.NewPacket(dataBz, ibcSeqNum, "srcPort", "srcChan", "provider-port", channelID, clienttypes.Height{}, 1),
		data,
	)
}

func executeOnRecvSlashPacket(t *testing.T, providerKeeper *keeper.Keeper, ctx sdk.Context,
	channelID string, ibcSeqNum uint64) exported.Acknowledgement {

	// Instantiate slash packet data and bytes
	data := testkeeper.GetNewSlashPacketData()
	dataBz, err := data.Marshal()
	require.NoError(t, err)

	return providerKeeper.OnRecvSlashPacket(
		ctx,
		channeltypes.NewPacket(dataBz, ibcSeqNum, "srcPort", "srcChan", "provider-port", channelID, clienttypes.Height{}, 1),
		data,
	)
}
