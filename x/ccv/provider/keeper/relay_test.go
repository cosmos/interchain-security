package keeper_test

import (
	"strings"
	"testing"
	"time"

	clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v7/modules/core/04-channel/types"
	ibctesting "github.com/cosmos/ibc-go/v7/testing"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	abci "github.com/cometbft/cometbft/abci/types"

	cryptotestutil "github.com/cosmos/interchain-security/v3/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/v3/testutil/keeper"
	"github.com/cosmos/interchain-security/v3/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/v3/x/ccv/types"
)

// TestQueueVSCPackets tests queueing validator set updates.
func TestQueueVSCPackets(t *testing.T) {
	_, _, key := ibctesting.GenerateKeys(t, 1)
	tmPubKey, _ := cryptocodec.ToTmProtoPublicKey(key)

	testCases := []struct {
		name                     string
		packets                  []ccv.ValidatorSetChangePacketData
		expectNextValsetUpdateId uint64
		expectedQueueSize        int
	}{
		{
			name:                     "no updates to send",
			packets:                  []ccv.ValidatorSetChangePacketData{},
			expectNextValsetUpdateId: 1,
			expectedQueueSize:        0,
		},
		{
			name: "have updates to send",
			packets: []ccv.ValidatorSetChangePacketData{
				{
					ValidatorUpdates: []abci.ValidatorUpdate{
						{PubKey: tmPubKey, Power: 1},
					},
					ValsetUpdateId: 1,
				},
			},
			expectNextValsetUpdateId: 1,
			expectedQueueSize:        1,
		},
	}

	chainID := "consumer"

	for _, tc := range testCases {
		keeperParams := testkeeper.NewInMemKeeperParams(t)
		ctx := keeperParams.Ctx

		ctrl := gomock.NewController(t)
		defer ctrl.Finish()
		mocks := testkeeper.NewMockedKeepers(ctrl)
		mockStakingKeeper := mocks.MockStakingKeeper

		mockUpdates := []abci.ValidatorUpdate{}
		if len(tc.packets) != 0 {
			mockUpdates = tc.packets[0].ValidatorUpdates
		}

		gomock.InOrder(
			mockStakingKeeper.EXPECT().GetValidatorUpdates(gomock.Eq(ctx)).Return(mockUpdates),
		)

		pk := testkeeper.NewInMemProviderKeeper(keeperParams, mocks)
		// no-op if tc.packets is empty
		pk.AppendPendingVSCPackets(ctx, chainID, tc.packets...)

		pk.QueueVSCPackets(ctx)
		pending := pk.GetPendingVSCPackets(ctx, chainID)
		require.Len(t, pending, tc.expectedQueueSize, "pending vsc queue mismatch (%v != %v) in case: '%s'", tc.expectedQueueSize, len(pending), tc.name)

		// next valset update ID -> default value in tests is 0
		// each call to QueueValidatorUpdates will increment the ValidatorUpdateID
		valUpdateID := pk.GetValidatorSetUpdateId(ctx)
		require.Equal(t, tc.expectNextValsetUpdateId, valUpdateID, "valUpdateID (%v != %v) mismatch in case: '%s'", tc.expectNextValsetUpdateId, valUpdateID, tc.name)
	}
}

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
	err := executeOnRecvVSCMaturedPacket(t, &providerKeeper, ctx, "channel-1", 1)
	require.NoError(t, err)

	// Assert that the packet data was queued for chain-1
	require.Equal(t, uint64(1), providerKeeper.GetThrottledPacketDataSize(ctx, "chain-1"))

	// chain-2 queue empty
	require.Equal(t, uint64(0), providerKeeper.GetThrottledPacketDataSize(ctx, "chain-2"))

	// Now queue a slash packet data instance for chain-2, then confirm the on recv method
	// queues the vsc matured behind the slash packet data
	err = providerKeeper.QueueThrottledSlashPacketData(ctx, "chain-2", 1, testkeeper.GetNewSlashPacketData())
	require.NoError(t, err)
	err = executeOnRecvVSCMaturedPacket(t, &providerKeeper, ctx, "channel-2", 2)
	require.NoError(t, err)
	require.Equal(t, uint64(2), providerKeeper.GetThrottledPacketDataSize(ctx, "chain-2"))

	// Chain-1 still has 1 packet data queued
	require.Equal(t, uint64(1), providerKeeper.GetThrottledPacketDataSize(ctx, "chain-1"))

	// Receive 5 more vsc matured packets for chain-2, then confirm chain-2 queue size is 7, chain-1 still size 1
	for i := 0; i < 5; i++ {
		err := executeOnRecvVSCMaturedPacket(t, &providerKeeper, ctx, "channel-2", uint64(i+3))
		require.NoError(t, err)
	}
	require.Equal(t, uint64(7), providerKeeper.GetThrottledPacketDataSize(ctx, "chain-2"))
	require.Equal(t, uint64(1), providerKeeper.GetThrottledPacketDataSize(ctx, "chain-1"))

	// Delete chain-2's data from its queue, then confirm the queue size is 0
	providerKeeper.DeleteThrottledPacketData(ctx, "chain-2", []uint64{1, 2, 3, 4, 5, 6, 7}...)
	require.Equal(t, uint64(0), providerKeeper.GetThrottledPacketDataSize(ctx, "chain-2"))

	// Execute on recv for chain-1, confirm v1 result ack is returned
	err = executeOnRecvVSCMaturedPacket(t, &providerKeeper, ctx, "channel-1", 1)
	require.NoError(t, err)

	// Now queue a slash packet data instance for chain-2, confirm v1 result ack is returned
	err = executeOnRecvVSCMaturedPacket(t, &providerKeeper, ctx, "channel-2", 2)
	require.NoError(t, err)
}

func TestHandleLeadingVSCMaturedPackets(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()
	providerKeeper.SetParams(ctx, providertypes.DefaultParams())

	vscData := getTenSampleVSCMaturedPacketData()

	// Set channel to chain, and chain to client mappings
	// (faking multiple established consumer channels)
	providerKeeper.SetChannelToChain(ctx, "channel-1", "chain-1")
	providerKeeper.SetConsumerClientId(ctx, "chain-1", "client-1")
	providerKeeper.SetChannelToChain(ctx, "channel-2", "chain-2")
	providerKeeper.SetConsumerClientId(ctx, "chain-2", "client-2")

	// Queue some leading vsc matured packet data for chain-1
	err := providerKeeper.QueueThrottledVSCMaturedPacketData(ctx, "chain-1", 1, vscData[0])
	require.NoError(t, err)
	err = providerKeeper.QueueThrottledVSCMaturedPacketData(ctx, "chain-1", 2, vscData[1])
	require.NoError(t, err)
	err = providerKeeper.QueueThrottledVSCMaturedPacketData(ctx, "chain-1", 3, vscData[2])
	require.NoError(t, err)

	// Queue some trailing slash packet data (and a couple more vsc matured)
	err = providerKeeper.QueueThrottledSlashPacketData(ctx, "chain-1", 4, testkeeper.GetNewSlashPacketData())
	require.NoError(t, err)
	err = providerKeeper.QueueThrottledSlashPacketData(ctx, "chain-1", 5, testkeeper.GetNewSlashPacketData())
	require.NoError(t, err)
	err = providerKeeper.QueueThrottledVSCMaturedPacketData(ctx, "chain-1", 6, vscData[3])
	require.NoError(t, err)
	err = providerKeeper.QueueThrottledVSCMaturedPacketData(ctx, "chain-1", 7, vscData[4])
	require.NoError(t, err)

	// Queue some leading vsc matured packet data for chain-2
	err = providerKeeper.QueueThrottledVSCMaturedPacketData(ctx, "chain-2", 1, vscData[5])
	require.NoError(t, err)
	err = providerKeeper.QueueThrottledVSCMaturedPacketData(ctx, "chain-2", 2, vscData[6])
	require.NoError(t, err)

	// And trailing slash packet data for chain-2
	err = providerKeeper.QueueThrottledSlashPacketData(ctx, "chain-2", 3, testkeeper.GetNewSlashPacketData())
	require.NoError(t, err)
	err = providerKeeper.QueueThrottledSlashPacketData(ctx, "chain-2", 4, testkeeper.GetNewSlashPacketData())

	require.NoError(t, err)

	// And one more trailing vsc matured packet for chain-2
	err = providerKeeper.QueueThrottledVSCMaturedPacketData(ctx, "chain-2", 5, vscData[7])
	require.NoError(t, err)

	// Set VSC Send timestamps for each recv vsc matured packet
	providerKeeper.SetVscSendTimestamp(ctx, "chain-1", vscData[0].ValsetUpdateId, time.Now())
	providerKeeper.SetVscSendTimestamp(ctx, "chain-1", vscData[1].ValsetUpdateId, time.Now())
	providerKeeper.SetVscSendTimestamp(ctx, "chain-1", vscData[2].ValsetUpdateId, time.Now())
	providerKeeper.SetVscSendTimestamp(ctx, "chain-1", vscData[3].ValsetUpdateId, time.Now())
	providerKeeper.SetVscSendTimestamp(ctx, "chain-1", vscData[4].ValsetUpdateId, time.Now())
	providerKeeper.SetVscSendTimestamp(ctx, "chain-2", vscData[5].ValsetUpdateId, time.Now())
	providerKeeper.SetVscSendTimestamp(ctx, "chain-2", vscData[6].ValsetUpdateId, time.Now())
	providerKeeper.SetVscSendTimestamp(ctx, "chain-2", vscData[7].ValsetUpdateId, time.Now())

	// Confirm each chain-specific queue has the expected number of packet data instances
	require.Equal(t, uint64(7), providerKeeper.GetThrottledPacketDataSize(ctx, "chain-1"))
	require.Equal(t, uint64(5), providerKeeper.GetThrottledPacketDataSize(ctx, "chain-2"))

	// Handle leading vsc matured packets and confirm queue sizes change for both chains
	providerKeeper.HandleLeadingVSCMaturedPackets(ctx)
	require.Equal(t, uint64(4), providerKeeper.GetThrottledPacketDataSize(ctx, "chain-1"))
	require.Equal(t, uint64(3), providerKeeper.GetThrottledPacketDataSize(ctx, "chain-2"))

	// Confirm the leading vsc matured packet data was handled for both chains,
	// but not the vsc matured packet data that trails slash data in the queue.
	// This assertion is made by checking that VSC Send timestamps were deleted for
	// handled vsc matured packet data.
	_, found := providerKeeper.GetVscSendTimestamp(ctx, "chain-1", vscData[0].ValsetUpdateId)
	require.False(t, found)
	_, found = providerKeeper.GetVscSendTimestamp(ctx, "chain-1", vscData[1].ValsetUpdateId)
	require.False(t, found)
	_, found = providerKeeper.GetVscSendTimestamp(ctx, "chain-1", vscData[2].ValsetUpdateId)
	require.False(t, found)
	_, found = providerKeeper.GetVscSendTimestamp(ctx, "chain-1", vscData[3].ValsetUpdateId)
	require.True(t, found)
	_, found = providerKeeper.GetVscSendTimestamp(ctx, "chain-1", vscData[4].ValsetUpdateId)
	require.True(t, found)

	_, found = providerKeeper.GetVscSendTimestamp(ctx, "chain-2", vscData[5].ValsetUpdateId)
	require.False(t, found)
	_, found = providerKeeper.GetVscSendTimestamp(ctx, "chain-2", vscData[6].ValsetUpdateId)
	require.False(t, found)
	_, found = providerKeeper.GetVscSendTimestamp(ctx, "chain-2", vscData[7].ValsetUpdateId)
	require.True(t, found)
}

// TestOnRecvSlashPacket tests the OnRecvSlashPacket method specifically for double-sign slash packets.
func TestOnRecvDoubleSignSlashPacket(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()
	providerKeeper.SetParams(ctx, providertypes.DefaultParams())

	// Set channel to chain (faking multiple established channels)
	providerKeeper.SetChannelToChain(ctx, "channel-1", "chain-1")
	providerKeeper.SetChannelToChain(ctx, "channel-2", "chain-2")

	// Generate a new slash packet data instance with double sign infraction type
	packetData := testkeeper.GetNewSlashPacketData()
	packetData.Infraction = stakingtypes.Infraction_INFRACTION_DOUBLE_SIGN

	// Set a block height for the valset update id in the generated packet data
	providerKeeper.SetValsetUpdateBlockHeight(ctx, packetData.ValsetUpdateId, uint64(15))

	// Receive the double-sign slash packet for chain-1 and confirm the expected acknowledgement
	ackResult, err := executeOnRecvSlashPacket(t, &providerKeeper, ctx, "channel-1", 1, packetData)
	require.Equal(t, ccv.V1Result, ackResult)
	require.NoError(t, err)

	// Nothing should be queued
	require.Equal(t, uint64(0), providerKeeper.GetThrottledPacketDataSize(ctx, "chain-1"))
	require.Equal(t, uint64(0), providerKeeper.GetThrottledPacketDataSize(ctx, "chain-2"))
	require.Equal(t, 0, len(providerKeeper.GetAllGlobalSlashEntries(ctx)))
	require.True(t, providerKeeper.GetSlashLog(ctx,
		providertypes.NewProviderConsAddress(packetData.Validator.Address)))

	// slash log should be empty for a random validator address in this testcase
	randomAddress := cryptotestutil.NewCryptoIdentityFromIntSeed(100).ProviderConsAddress()
	require.False(t, providerKeeper.GetSlashLog(ctx, randomAddress))
}

// TestOnRecvSlashPacket tests the OnRecvSlashPacket method specifically for downtime slash packets,
// and how the method interacts with the parent and per-chain slash packet queues.
func TestOnRecvDowntimeSlashPacket(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()
	providerKeeper.SetParams(ctx, providertypes.DefaultParams())

	// Set channel to chain (faking multiple established channels)
	providerKeeper.SetChannelToChain(ctx, "channel-1", "chain-1")
	providerKeeper.SetChannelToChain(ctx, "channel-2", "chain-2")

	// Generate a new slash packet data instance with downtime infraction type
	packetData := testkeeper.GetNewSlashPacketData()
	packetData.Infraction = stakingtypes.Infraction_INFRACTION_DOWNTIME

	// Set a block height for the valset update id in the generated packet data
	providerKeeper.SetValsetUpdateBlockHeight(ctx, packetData.ValsetUpdateId, uint64(15))

	// Receive the downtime slash packet for chain-1 at time.Now()
	ctx = ctx.WithBlockTime(time.Now())
	ackResult, err := executeOnRecvSlashPacket(t, &providerKeeper, ctx, "channel-1", 1, packetData)
	require.Equal(t, ccv.V1Result, ackResult)
	require.NoError(t, err)

	// Confirm an entry was added to the global queue, and pending packet data was added to the per-chain queue
	globalEntries := providerKeeper.GetAllGlobalSlashEntries(ctx) // parent queue
	require.Equal(t, 1, len(globalEntries))
	require.Equal(t, "chain-1", globalEntries[0].ConsumerChainID)
	require.Equal(t, uint64(1), providerKeeper.GetThrottledPacketDataSize(ctx, "chain-1")) // per chain queue

	// Generate a new downtime packet data instance with downtime infraction type
	packetData = testkeeper.GetNewSlashPacketData()
	packetData.Infraction = stakingtypes.Infraction_INFRACTION_DOWNTIME

	// Set a block height for the valset update id in the generated packet data
	providerKeeper.SetValsetUpdateBlockHeight(ctx, packetData.ValsetUpdateId, uint64(15))

	// Receive a downtime slash packet for chain-2 at time.Now(Add(1 *time.Hour))
	ctx = ctx.WithBlockTime(time.Now().Add(1 * time.Hour))
	ackResult, err = executeOnRecvSlashPacket(t, &providerKeeper, ctx, "channel-2", 2, packetData)
	require.Equal(t, ccv.V1Result, ackResult)
	require.NoError(t, err)

	// Confirm sizes of parent queue and both per-chain queues
	globalEntries = providerKeeper.GetAllGlobalSlashEntries(ctx)
	require.Equal(t, 2, len(globalEntries))
	require.Equal(t, "chain-1", globalEntries[0].ConsumerChainID)
	require.Equal(t, "chain-2", globalEntries[1].ConsumerChainID)
	require.Equal(t, uint64(1), providerKeeper.GetThrottledPacketDataSize(ctx, "chain-1")) // per chain queue
	require.Equal(t, uint64(1), providerKeeper.GetThrottledPacketDataSize(ctx, "chain-2")) // per chain queue
}

func executeOnRecvVSCMaturedPacket(t *testing.T, providerKeeper *keeper.Keeper, ctx sdk.Context,
	channelID string, ibcSeqNum uint64,
) error {
	t.Helper()
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
	channelID string, ibcSeqNum uint64, packetData ccv.SlashPacketData,
) (ccv.PacketAckResult, error) {
	t.Helper()
	// Instantiate slash packet data and bytes
	dataBz, err := packetData.Marshal()
	require.NoError(t, err)

	return providerKeeper.OnRecvSlashPacket(
		ctx,
		channeltypes.NewPacket(dataBz, ibcSeqNum, "srcPort", "srcChan", "provider-port", channelID, clienttypes.Height{}, 1),
		packetData,
	)
}

// TestValidateSlashPacket tests ValidateSlashPacket.
func TestValidateSlashPacket(t *testing.T) {
	validVscID := uint64(98)

	testCases := []struct {
		name       string
		packetData ccv.SlashPacketData
		expectErr  bool
	}{
		{
			"no block height found for given vscID",
			ccv.SlashPacketData{ValsetUpdateId: 61},
			true,
		},
		{
			"valid double sign packet with non-zero vscID",
			ccv.SlashPacketData{ValsetUpdateId: validVscID, Infraction: stakingtypes.Infraction_INFRACTION_DOUBLE_SIGN},
			false,
		},
		{
			"valid downtime packet with non-zero vscID",
			ccv.SlashPacketData{ValsetUpdateId: validVscID, Infraction: stakingtypes.Infraction_INFRACTION_DOWNTIME},
			false,
		},
		{
			"valid double sign packet with zero vscID",
			ccv.SlashPacketData{ValsetUpdateId: 0, Infraction: stakingtypes.Infraction_INFRACTION_DOUBLE_SIGN},
			false,
		},
		{
			"valid downtime packet with zero vscID",
			ccv.SlashPacketData{ValsetUpdateId: 0, Infraction: stakingtypes.Infraction_INFRACTION_DOWNTIME},
			false,
		},
	}

	for _, tc := range testCases {
		providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(
			t, testkeeper.NewInMemKeeperParams(t))
		defer ctrl.Finish()

		packet := channeltypes.Packet{DestinationChannel: "channel-9"}

		// Pseudo setup ccv channel for channel ID specified in packet.
		providerKeeper.SetChannelToChain(ctx, "channel-9", "consumer-chain-id")

		// Setup init chain height for consumer (allowing 0 vscID to be valid).
		providerKeeper.SetInitChainHeight(ctx, "consumer-chain-id", uint64(89))

		// Setup valset update ID to block height mapping using var instantiated above.
		providerKeeper.SetValsetUpdateBlockHeight(ctx, validVscID, uint64(100))

		// Test error behavior as specified in tc.
		err := providerKeeper.ValidateSlashPacket(ctx, "consumer-chain-id", packet, tc.packetData)
		if tc.expectErr {
			require.Error(t, err, "expected error in case: '%s'", tc.name)
		} else {
			require.NoError(t, err, "unexpected error in case: '%s'", tc.name)
		}
	}
}

// TestHandleSlashPacket tests the handling of slash packets.
// Note that only downtime slash packets are processed by HandleSlashPacket.
func TestHandleSlashPacket(t *testing.T) {
	chainId := "consumer-id"
	validVscID := uint64(234)
	providerConsAddr := cryptotestutil.NewCryptoIdentityFromIntSeed(7842334).ProviderConsAddress()
	consumerConsAddr := cryptotestutil.NewCryptoIdentityFromIntSeed(784987634).ConsumerConsAddress()

	testCases := []struct {
		name       string
		packetData ccv.SlashPacketData
		// The mocks that we expect to be called for the specified packet data.
		expectedCalls        func(sdk.Context, testkeeper.MockedKeepers, ccv.SlashPacketData) []*gomock.Call
		expectedSlashAcksLen int
	}{
		{
			"unfound validator",
			ccv.SlashPacketData{
				Validator:      abci.Validator{Address: consumerConsAddr.ToSdkConsAddr()},
				ValsetUpdateId: validVscID,
				Infraction:     stakingtypes.Infraction_INFRACTION_DOWNTIME,
			},
			func(ctx sdk.Context, mocks testkeeper.MockedKeepers,
				expectedPacketData ccv.SlashPacketData,
			) []*gomock.Call {
				return []*gomock.Call{
					// We only expect a single call to GetValidatorByConsAddr.
					// Method will return once validator is not found.
					mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(
						ctx, providerConsAddr.ToSdkConsAddr()).Return(
						stakingtypes.Validator{}, false, // false = Not found.
					).Times(1),
				}
			},
			0,
		},
		{
			"found, but tombstoned validator",
			ccv.SlashPacketData{
				Validator:      abci.Validator{Address: consumerConsAddr.ToSdkConsAddr()},
				ValsetUpdateId: validVscID,
				Infraction:     stakingtypes.Infraction_INFRACTION_DOWNTIME,
			},
			func(ctx sdk.Context, mocks testkeeper.MockedKeepers,
				expectedPacketData ccv.SlashPacketData,
			) []*gomock.Call {
				return []*gomock.Call{
					mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(
						ctx, providerConsAddr.ToSdkConsAddr()).Return(
						stakingtypes.Validator{}, true, // true = Found.
					).Times(1),
					// Execution will stop after this call as validator is tombstoned.
					mocks.MockSlashingKeeper.EXPECT().IsTombstoned(ctx,
						providerConsAddr.ToSdkConsAddr()).Return(true).Times(1),
				}
			},
			0,
		},
		{
			"drop packet when infraction height not found",
			ccv.SlashPacketData{
				Validator:      abci.Validator{Address: consumerConsAddr.ToSdkConsAddr()},
				ValsetUpdateId: 78, // Keeper doesn't have a height mapped to this vscID.
				Infraction:     stakingtypes.Infraction_INFRACTION_DOWNTIME,
			},

			func(ctx sdk.Context, mocks testkeeper.MockedKeepers,
				expectedPacketData ccv.SlashPacketData,
			) []*gomock.Call {
				return []*gomock.Call{
					mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(
						ctx, providerConsAddr.ToSdkConsAddr()).Return(
						stakingtypes.Validator{}, true,
					).Times(1),

					mocks.MockSlashingKeeper.EXPECT().IsTombstoned(ctx,
						providerConsAddr.ToSdkConsAddr()).Return(false).Times(1),
				}
			},
			0,
		},
		{
			"full downtime packet handling, uses init chain height and non-jailed validator",
			*ccv.NewSlashPacketData(
				abci.Validator{Address: consumerConsAddr.ToSdkConsAddr()},
				0, // ValsetUpdateId = 0 uses init chain height.
				stakingtypes.Infraction_INFRACTION_DOWNTIME),
			func(ctx sdk.Context, mocks testkeeper.MockedKeepers,
				expectedPacketData ccv.SlashPacketData,
			) []*gomock.Call {
				return testkeeper.GetMocksForHandleSlashPacket(
					ctx, mocks,
					providerConsAddr,                      // expected provider cons addr returned from GetProviderAddrFromConsumerAddr
					stakingtypes.Validator{Jailed: false}, // staking keeper val to return
					true)                                  // expectJailing = true
			},
			1,
		},
		{
			"full downtime packet handling, uses valid vscID and jailed validator",
			*ccv.NewSlashPacketData(
				abci.Validator{Address: consumerConsAddr.ToSdkConsAddr()},
				validVscID,
				stakingtypes.Infraction_INFRACTION_DOWNTIME),
			func(ctx sdk.Context, mocks testkeeper.MockedKeepers,
				expectedPacketData ccv.SlashPacketData,
			) []*gomock.Call {
				return testkeeper.GetMocksForHandleSlashPacket(
					ctx, mocks,
					providerConsAddr,                     // expected provider cons addr returned from GetProviderAddrFromConsumerAddr
					stakingtypes.Validator{Jailed: true}, // staking keeper val to return
					false)                                // expectJailing = false, validator is already jailed.
			},
			1,
		},
		// Note: double-sign slash packet handling should not occur, see OnRecvSlashPacket.
	}

	for _, tc := range testCases {

		providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(
			t, testkeeper.NewInMemKeeperParams(t))

		// Setup expected mock calls
		gomock.InOrder(tc.expectedCalls(ctx, mocks, tc.packetData)...)

		// Setup init chain height and a single valid valset update ID to block height mapping.
		providerKeeper.SetInitChainHeight(ctx, chainId, 5)
		providerKeeper.SetValsetUpdateBlockHeight(ctx, validVscID, 99)

		// Setup consumer address to provider address mapping.
		require.NotEmpty(t, tc.packetData.Validator.Address)
		providerKeeper.SetValidatorByConsumerAddr(ctx, chainId, consumerConsAddr, providerConsAddr)

		// Execute method and assert expected mock calls.
		providerKeeper.HandleSlashPacket(ctx, chainId, tc.packetData)

		require.Equal(t, tc.expectedSlashAcksLen, len(providerKeeper.GetSlashAcks(ctx, chainId)))

		if tc.expectedSlashAcksLen == 1 {
			// must match the consumer address
			require.Equal(t, consumerConsAddr.String(), providerKeeper.GetSlashAcks(ctx, chainId)[0])
			require.NotEqual(t, providerConsAddr.String(), providerKeeper.GetSlashAcks(ctx, chainId)[0])
			require.NotEqual(t, providerConsAddr.String(), consumerConsAddr.String())
		}

		ctrl.Finish()
	}
}

// TestHandleVSCMaturedPacket tests the handling of VSCMatured packets.
// Note that this method also tests the behaviour of AfterUnbondingInitiated.
func TestHandleVSCMaturedPacket(t *testing.T) {
	pk, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// Init vscID
	pk.SetValidatorSetUpdateId(ctx, 1)

	// Start first unbonding without any consumers registered
	var unbondingOpId uint64 = 1
	err := pk.Hooks().AfterUnbondingInitiated(ctx, unbondingOpId)
	require.NoError(t, err)
	// Check that no unbonding op was stored
	_, found := pk.GetUnbondingOp(ctx, unbondingOpId)
	require.False(t, found)

	// Increment vscID
	pk.IncrementValidatorSetUpdateId(ctx)
	require.Equal(t, uint64(2), pk.GetValidatorSetUpdateId(ctx))

	// Registered first consumer
	pk.SetConsumerClientId(ctx, "chain-1", "client-1")

	// Start second unbonding
	unbondingOpId = 2
	gomock.InOrder(
		mocks.MockStakingKeeper.EXPECT().PutUnbondingOnHold(ctx, unbondingOpId).Return(nil),
	)
	err = pk.Hooks().AfterUnbondingInitiated(ctx, unbondingOpId)
	require.NoError(t, err)
	// Check that an unbonding op was stored
	expectedChains := []string{"chain-1"}
	unbondingOp, found := pk.GetUnbondingOp(ctx, unbondingOpId)
	require.True(t, found)
	require.Equal(t, unbondingOpId, unbondingOp.Id)
	require.Equal(t, expectedChains, unbondingOp.UnbondingConsumerChains)
	// Check that the unbonding op index was stored
	expectedUnbondingOpIds := []uint64{unbondingOpId}
	ids, found := pk.GetUnbondingOpIndex(ctx, "chain-1", pk.GetValidatorSetUpdateId(ctx))
	require.True(t, found)
	require.Equal(t, expectedUnbondingOpIds, ids)

	// Increment vscID
	pk.IncrementValidatorSetUpdateId(ctx)
	require.Equal(t, uint64(3), pk.GetValidatorSetUpdateId(ctx))

	// Registered second consumer
	pk.SetConsumerClientId(ctx, "chain-2", "client-2")

	// Start third and fourth unbonding
	unbondingOpIds := []uint64{3, 4}
	for _, id := range unbondingOpIds {
		gomock.InOrder(
			mocks.MockStakingKeeper.EXPECT().PutUnbondingOnHold(ctx, id).Return(nil),
		)
		err = pk.Hooks().AfterUnbondingInitiated(ctx, id)
		require.NoError(t, err)
	}
	// Check that the unbonding ops were stored
	expectedChains = []string{"chain-1", "chain-2"}
	for _, id := range unbondingOpIds {
		unbondingOp, found = pk.GetUnbondingOp(ctx, id)
		require.True(t, found)
		require.Equal(t, id, unbondingOp.Id)
		require.Equal(t, expectedChains, unbondingOp.UnbondingConsumerChains)
	}
	// Check that the unbonding op index was stored
	for _, chainID := range expectedChains {
		ids, found := pk.GetUnbondingOpIndex(ctx, chainID, pk.GetValidatorSetUpdateId(ctx))
		require.True(t, found)
		require.Equal(t, unbondingOpIds, ids)
	}

	// Handle VSCMatured packet from chain-1 for vscID 1.
	// Note that no VSCPacket was sent as the chain was not yet registered,
	// but the code should still work
	pk.HandleVSCMaturedPacket(ctx, "chain-1", ccv.VSCMaturedPacketData{ValsetUpdateId: 1})
	require.Empty(t, pk.ConsumeMaturedUnbondingOps(ctx))

	// Handle VSCMatured packet from chain-1 for vscID 2.
	pk.HandleVSCMaturedPacket(ctx, "chain-1", ccv.VSCMaturedPacketData{ValsetUpdateId: 2})
	// Check that the unbonding operation with ID=2 can complete
	require.Equal(t, []uint64{2}, pk.ConsumeMaturedUnbondingOps(ctx))
	// Check that the unbonding op index was removed
	_, found = pk.GetUnbondingOpIndex(ctx, "chain-1", 2)
	require.False(t, found)

	// Handle VSCMatured packet from chain-2 for vscID 3.
	pk.HandleVSCMaturedPacket(ctx, "chain-2", ccv.VSCMaturedPacketData{ValsetUpdateId: 3})
	// Check that the unbonding operations with IDs 3 and 4 no longer wait for chain-2
	expectedChains = []string{"chain-1"}
	unbondingOpIds = []uint64{3, 4}
	for _, id := range unbondingOpIds {
		unbondingOp, found := pk.GetUnbondingOp(ctx, id)
		require.True(t, found)
		require.Equal(t, id, unbondingOp.Id)
		require.Equal(t, expectedChains, unbondingOp.UnbondingConsumerChains)
	}
	// Check that no unbonding operation can complete
	require.Empty(t, pk.ConsumeMaturedUnbondingOps(ctx))
	// Check that the unbonding op index was removed
	_, found = pk.GetUnbondingOpIndex(ctx, "chain-2", 3)
	require.False(t, found)

	// Handle VSCMatured packet from chain-1 for vscID 3.
	pk.HandleVSCMaturedPacket(ctx, "chain-1", ccv.VSCMaturedPacketData{ValsetUpdateId: 3})
	// Check that the unbonding operations with IDs 3 and 4 can complete
	require.Equal(t, unbondingOpIds, pk.ConsumeMaturedUnbondingOps(ctx))
	// Check that the unbonding op index was removed
	_, found = pk.GetUnbondingOpIndex(ctx, "chain-1", 3)
	require.False(t, found)
}

// TestSendVSCPacketsToChainFailure tests the SendVSCPacketsToChain method failing
func TestSendVSCPacketsToChainFailure(t *testing.T) {
	// Keeper setup
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()
	providerKeeper.SetParams(ctx, providertypes.DefaultParams())

	// Append mocks for full consumer setup
	mockCalls := testkeeper.GetMocksForSetConsumerChain(ctx, &mocks, "consumerChainID")

	// Set 3 pending vsc packets
	providerKeeper.AppendPendingVSCPackets(ctx, "consumerChainID", []ccv.ValidatorSetChangePacketData{{}, {}, {}}...)

	// append mocks for the channel keeper to return an error
	mockCalls = append(mockCalls,
		mocks.MockChannelKeeper.EXPECT().GetChannel(ctx, ccv.ProviderPortID,
			"CCVChannelID").Return(channeltypes.Channel{}, false).Times(1),
	)

	// Append mocks for expected call to StopConsumerChain
	mockCalls = append(mockCalls, testkeeper.GetMocksForStopConsumerChainWithCloseChannel(ctx, &mocks)...)

	// Assert mock calls hit
	gomock.InOrder(mockCalls...)

	// Execute setup
	err := providerKeeper.SetConsumerChain(ctx, "channelID")
	require.NoError(t, err)
	providerKeeper.SetConsumerClientId(ctx, "consumerChainID", "clientID")

	// No panic should occur, StopConsumerChain should be called
	providerKeeper.SendVSCPacketsToChain(ctx, "consumerChainID", "CCVChannelID")

	// Pending VSC packets should be deleted in StopConsumerChain
	require.Empty(t, providerKeeper.GetPendingVSCPackets(ctx, "consumerChainID"))
}

// TestOnTimeoutPacketWithNoChainFound tests the `OnTimeoutPacket` method fails when no chain is found
func TestOnTimeoutPacketWithNoChainFound(t *testing.T) {
	// Keeper setup
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// We do not `SetChannelToChain` for "channelID" and therefore `OnTimeoutPacket` fails
	packet := channeltypes.Packet{
		SourceChannel: "channelID",
	}
	err := providerKeeper.OnTimeoutPacket(ctx, packet)
	require.Error(t, err)
	require.True(t, strings.Contains(err.Error(), channeltypes.ErrInvalidChannel.Error()))
}

// TestOnTimeoutPacketStopsChain tests that the chain is stopped in case of a timeout
func TestOnTimeoutPacketStopsChain(t *testing.T) {
	// Keeper setup
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()
	providerKeeper.SetParams(ctx, providertypes.DefaultParams())

	testkeeper.SetupForStoppingConsumerChain(t, ctx, &providerKeeper, mocks)

	packet := channeltypes.Packet{
		SourceChannel: "channelID",
	}
	err := providerKeeper.OnTimeoutPacket(ctx, packet)

	testkeeper.TestProviderStateIsCleanedAfterConsumerChainIsStopped(t, ctx, providerKeeper, "chainID", "channelID")
	require.NoError(t, err)
}

// TestOnAcknowledgementPacketWithNoAckError tests `OnAcknowledgementPacket` when the underlying ack contains no error
func TestOnAcknowledgementPacketWithNoAckError(t *testing.T) {
	// Keeper setup
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	ack := channeltypes.Acknowledgement{Response: &channeltypes.Acknowledgement_Result{Result: []byte{}}}
	err := providerKeeper.OnAcknowledgementPacket(ctx, channeltypes.Packet{}, ack)
	require.NoError(t, err)
}

// TestOnAcknowledgementPacketWithAckError tests `OnAcknowledgementPacket` when the underlying ack contains an error
func TestOnAcknowledgementPacketWithAckError(t *testing.T) {
	// Keeper setup
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()
	providerKeeper.SetParams(ctx, providertypes.DefaultParams())

	// test that `OnAcknowledgementPacket` returns an error if the ack contains an error and the channel is unknown
	ackError := channeltypes.Acknowledgement{Response: &channeltypes.Acknowledgement_Error{Error: "some error"}}
	err := providerKeeper.OnAcknowledgementPacket(ctx, channeltypes.Packet{}, ackError)
	require.Error(t, err)
	require.True(t, strings.Contains(err.Error(), providertypes.ErrUnknownConsumerChannelId.Error()))

	// test that we stop the consumer chain when `OnAcknowledgementPacket` returns an error and the chain is found
	testkeeper.SetupForStoppingConsumerChain(t, ctx, &providerKeeper, mocks)
	packet := channeltypes.Packet{
		SourceChannel: "channelID",
	}

	err = providerKeeper.OnAcknowledgementPacket(ctx, packet, ackError)

	testkeeper.TestProviderStateIsCleanedAfterConsumerChainIsStopped(t, ctx, providerKeeper, "chainID", "channelID")
	require.NoError(t, err)
}
