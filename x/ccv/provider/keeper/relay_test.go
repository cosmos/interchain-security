package keeper_test

import (
	"testing"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	exported "github.com/cosmos/ibc-go/v3/modules/core/exported"
	"github.com/cosmos/interchain-security/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	"github.com/golang/mock/gomock"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	ibcsimapp "github.com/cosmos/ibc-go/v3/testing/simapp"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	abci "github.com/tendermint/tendermint/abci/types"

	"github.com/stretchr/testify/require"
)

// TestQueueVSCPackets tests queueing validator set updates.
func TestQueueVSCPackets(t *testing.T) {
	key := ibcsimapp.CreateTestPubKeys(1)[0]
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
	ack := executeOnRecvVSCMaturedPacket(t, &providerKeeper, ctx, "channel-1", 1)
	require.Equal(t, channeltypes.NewResultAcknowledgement([]byte{byte(1)}), ack)

	// Assert that the packet data was queued for chain-1
	require.Equal(t, uint64(1), providerKeeper.GetThrottledPacketDataSize(ctx, "chain-1"))

	// chain-2 queue empty
	require.Equal(t, uint64(0), providerKeeper.GetThrottledPacketDataSize(ctx, "chain-2"))

	// Now queue a slash packet data instance for chain-2, then confirm the on recv method
	// queues the vsc matured behind the slash packet data
	providerKeeper.QueueThrottledSlashPacketData(ctx, "chain-2", 1, testkeeper.GetNewSlashPacketData())
	ack = executeOnRecvVSCMaturedPacket(t, &providerKeeper, ctx, "channel-2", 2)
	require.Equal(t, channeltypes.NewResultAcknowledgement([]byte{byte(1)}), ack)
	require.Equal(t, uint64(2), providerKeeper.GetThrottledPacketDataSize(ctx, "chain-2"))

	// Chain-1 still has 1 packet data queued
	require.Equal(t, uint64(1), providerKeeper.GetThrottledPacketDataSize(ctx, "chain-1"))

	// Receive 5 more vsc matured packets for chain-2, then confirm chain-2 queue size is 7, chain-1 still size 1
	for i := 0; i < 5; i++ {
		ack = executeOnRecvVSCMaturedPacket(t, &providerKeeper, ctx, "channel-2", uint64(i+3))
		require.Equal(t, channeltypes.NewResultAcknowledgement([]byte{byte(1)}), ack)
	}
	require.Equal(t, uint64(7), providerKeeper.GetThrottledPacketDataSize(ctx, "chain-2"))
	require.Equal(t, uint64(1), providerKeeper.GetThrottledPacketDataSize(ctx, "chain-1"))

	// Delete chain-2's data from its queue, then confirm the queue size is 0
	providerKeeper.DeleteThrottledPacketData(ctx, "chain-2", []uint64{1, 2, 3, 4, 5, 6, 7}...)
	require.Equal(t, uint64(0), providerKeeper.GetThrottledPacketDataSize(ctx, "chain-2"))
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
	providerKeeper.QueueThrottledVSCMaturedPacketData(ctx, "chain-1", 1, vscData[0])
	providerKeeper.QueueThrottledVSCMaturedPacketData(ctx, "chain-1", 2, vscData[1])
	providerKeeper.QueueThrottledVSCMaturedPacketData(ctx, "chain-1", 3, vscData[2])

	// Queue some trailing slash packet data (and a couple more vsc matured)
	providerKeeper.QueueThrottledSlashPacketData(ctx, "chain-1", 4, testkeeper.GetNewSlashPacketData())
	providerKeeper.QueueThrottledSlashPacketData(ctx, "chain-1", 5, testkeeper.GetNewSlashPacketData())
	providerKeeper.QueueThrottledVSCMaturedPacketData(ctx, "chain-1", 6, vscData[3])
	providerKeeper.QueueThrottledVSCMaturedPacketData(ctx, "chain-1", 7, vscData[4])

	// Queue some leading vsc matured packet data for chain-2
	providerKeeper.QueueThrottledVSCMaturedPacketData(ctx, "chain-2", 1, vscData[5])
	providerKeeper.QueueThrottledVSCMaturedPacketData(ctx, "chain-2", 2, vscData[6])

	// And trailing slash packet data for chain-2
	providerKeeper.QueueThrottledSlashPacketData(ctx, "chain-2", 3, testkeeper.GetNewSlashPacketData())
	providerKeeper.QueueThrottledSlashPacketData(ctx, "chain-2", 4, testkeeper.GetNewSlashPacketData())

	// And one more trailing vsc matured packet for chain-2
	providerKeeper.QueueThrottledVSCMaturedPacketData(ctx, "chain-2", 5, vscData[7])

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

// TestOnRecvSlashPacket tests the OnRecvSlashPacket method, and how it interacts with the
// parent and per-chain slash packet queues.
func TestOnRecvSlashPacket(t *testing.T) {

	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()
	providerKeeper.SetParams(ctx, providertypes.DefaultParams())

	// Set channel to chain (faking multiple established channels)
	providerKeeper.SetChannelToChain(ctx, "channel-1", "chain-1")
	providerKeeper.SetChannelToChain(ctx, "channel-2", "chain-2")

	// Generate a new slash packet data instance with valid infraction type
	packetData := testkeeper.GetNewSlashPacketData()
	packetData.Infraction = stakingtypes.DoubleSign

	// Set a block height for the valset update id in the generated packet data
	providerKeeper.SetValsetUpdateBlockHeight(ctx, packetData.ValsetUpdateId, uint64(15))

	// Receive a slash packet for chain-1 at time.Now()
	ctx = ctx.WithBlockTime(time.Now())
	ack := executeOnRecvSlashPacket(t, &providerKeeper, ctx, "channel-1", 1, packetData)
	require.Equal(t, channeltypes.NewResultAcknowledgement([]byte{byte(1)}), ack)

	// Confirm an entry was added to the global queue, and pending packet data was added to the per-chain queue
	globalEntries := providerKeeper.GetAllGlobalSlashEntries(ctx) // parent queue
	require.Equal(t, 1, len(globalEntries))
	require.Equal(t, "chain-1", globalEntries[0].ConsumerChainID)
	require.Equal(t, uint64(1), providerKeeper.GetThrottledPacketDataSize(ctx, "chain-1")) // per chain queue

	// Generate a new packet data instance with valid infraction type
	packetData = testkeeper.GetNewSlashPacketData()
	packetData.Infraction = stakingtypes.Downtime

	// Set a block height for the valset update id in the generated packet data
	providerKeeper.SetValsetUpdateBlockHeight(ctx, packetData.ValsetUpdateId, uint64(15))

	// Receive a slash packet for chain-2 at time.Now(Add(1 *time.Hour))
	ctx = ctx.WithBlockTime(time.Now().Add(1 * time.Hour))
	ack = executeOnRecvSlashPacket(t, &providerKeeper, ctx, "channel-2", 2, packetData)
	require.Equal(t, channeltypes.NewResultAcknowledgement([]byte{byte(1)}), ack)

	// Confirm sizes of parent queue and both per-chain queues
	globalEntries = providerKeeper.GetAllGlobalSlashEntries(ctx)
	require.Equal(t, 2, len(globalEntries))
	require.Equal(t, "chain-1", globalEntries[0].ConsumerChainID)
	require.Equal(t, "chain-2", globalEntries[1].ConsumerChainID)
	require.Equal(t, uint64(1), providerKeeper.GetThrottledPacketDataSize(ctx, "chain-1")) // per chain queue
	require.Equal(t, uint64(1), providerKeeper.GetThrottledPacketDataSize(ctx, "chain-2")) // per chain queue
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
	channelID string, ibcSeqNum uint64, packetData ccv.SlashPacketData) exported.Acknowledgement {

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
		errType    error
	}{
		{"no block height found for given vscID",
			ccv.SlashPacketData{ValsetUpdateId: 61},
			true,
			providertypes.ErrSlashPacketInfractionHeightInvalid},
		{"non-set infraction type",
			ccv.SlashPacketData{ValsetUpdateId: validVscID},
			true,
			providertypes.ErrSlashPacketInfractionTypeInvalid},
		{"invalid infraction type",
			ccv.SlashPacketData{ValsetUpdateId: validVscID, Infraction: stakingtypes.MaxMonikerLength},
			true,
			providertypes.ErrSlashPacketInfractionTypeInvalid},
		{"valid double sign packet with non-zero vscID",
			ccv.SlashPacketData{ValsetUpdateId: validVscID, Infraction: stakingtypes.DoubleSign},
			false,
			nil},
		{"valid downtime packet with non-zero vscID",
			ccv.SlashPacketData{ValsetUpdateId: validVscID, Infraction: stakingtypes.Downtime},
			false,
			nil},
		{"valid double sign packet with zero vscID",
			ccv.SlashPacketData{ValsetUpdateId: 0, Infraction: stakingtypes.DoubleSign},
			false,
			nil},
		{"valid downtime packet with zero vscID",
			ccv.SlashPacketData{ValsetUpdateId: 0, Infraction: stakingtypes.Downtime},
			false,
			nil},
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
			require.ErrorIs(t, err, tc.errType, "incorrect expected error type: '%s' in case: %s", tc.errType, tc.name)
		} else {
			require.NoError(t, err, "unexpected error in case: '%s'", tc.name)
		}
	}
}

// TestHandleSlashPacket tests the handling of slash packets.
func TestHandleSlashPacket(t *testing.T) {

	chainId := "consumer-id"
	validVscID := uint64(234)

	testCases := []struct {
		name       string
		packetData ccv.SlashPacketData
		// The mocks that we expect to be called for the specified packet data.
		expectedCalls func(sdk.Context, testkeeper.MockedKeepers, ccv.SlashPacketData) []*gomock.Call
	}{
		{
			"not found validator",
			ccv.SlashPacketData{},
			func(ctx sdk.Context, mocks testkeeper.MockedKeepers,
				expectedPacketData ccv.SlashPacketData,
			) []*gomock.Call {
				return []*gomock.Call{
					// We only expect a single call to GetValidatorByConsAddr.
					// Method will return once validator is not found.
					mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(
						ctx, sdk.ConsAddress(expectedPacketData.Validator.Address)).Return(
						stakingtypes.Validator{}, false, // false = Not found.
					).Times(1),
				}
			},
		},
		{
			"found, but tombstoned validator",
			ccv.SlashPacketData{},
			func(ctx sdk.Context, mocks testkeeper.MockedKeepers,
				expectedPacketData ccv.SlashPacketData,
			) []*gomock.Call {
				return []*gomock.Call{
					mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(
						ctx, sdk.ConsAddress(expectedPacketData.Validator.Address)).Return(
						stakingtypes.Validator{}, true, // true = Found.
					).Times(1),
					// Execution will stop after this call as validator is tombstoned.
					mocks.MockSlashingKeeper.EXPECT().IsTombstoned(ctx,
						sdk.ConsAddress(expectedPacketData.Validator.Address)).Return(true).Times(1),
				}
			},
		},
		{
			"drop packet when infraction height not found",
			ccv.SlashPacketData{ValsetUpdateId: 78}, // Keeper doesn't have a height mapped to this vscID.
			func(ctx sdk.Context, mocks testkeeper.MockedKeepers,
				expectedPacketData ccv.SlashPacketData,
			) []*gomock.Call {
				return []*gomock.Call{

					mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(
						ctx, sdk.ConsAddress(expectedPacketData.Validator.Address)).Return(
						stakingtypes.Validator{}, true,
					).Times(1),

					mocks.MockSlashingKeeper.EXPECT().IsTombstoned(ctx,
						sdk.ConsAddress(expectedPacketData.Validator.Address)).Return(false).Times(1),
				}
			},
		},
		{
			"full downtime packet handling, uses init chain height and non-jailed validator",
			*ccv.NewSlashPacketData(abci.Validator{}, 0, stakingtypes.Downtime), // ValsetUpdateId = 0 uses init chain height.
			func(ctx sdk.Context, mocks testkeeper.MockedKeepers,
				expectedPacketData ccv.SlashPacketData,
			) []*gomock.Call {
				return testkeeper.GetMocksForHandleSlashPacket(
					ctx, mocks, expectedPacketData, stakingtypes.Validator{Jailed: false})
			},
		},
		{
			"full downtime packet handling, uses valid vscID and jailed validator",
			*ccv.NewSlashPacketData(abci.Validator{}, validVscID, stakingtypes.Downtime),
			func(ctx sdk.Context, mocks testkeeper.MockedKeepers,
				expectedPacketData ccv.SlashPacketData,
			) []*gomock.Call {
				return testkeeper.GetMocksForHandleSlashPacket(
					ctx, mocks, expectedPacketData, stakingtypes.Validator{Jailed: true})
			},
		},
		{
			"full double sign packet handling, uses init chain height and jailed validator",
			*ccv.NewSlashPacketData(abci.Validator{}, 0, stakingtypes.DoubleSign),
			func(ctx sdk.Context, mocks testkeeper.MockedKeepers,
				expectedPacketData ccv.SlashPacketData,
			) []*gomock.Call {
				return testkeeper.GetMocksForHandleSlashPacket(
					ctx, mocks, expectedPacketData, stakingtypes.Validator{Jailed: true})
			},
		},
		{
			"full double sign packet handling, uses valid vsc id and non-jailed validator",
			*ccv.NewSlashPacketData(abci.Validator{}, validVscID, stakingtypes.DoubleSign),
			func(ctx sdk.Context, mocks testkeeper.MockedKeepers,
				expectedPacketData ccv.SlashPacketData,
			) []*gomock.Call {
				return testkeeper.GetMocksForHandleSlashPacket(
					ctx, mocks, expectedPacketData, stakingtypes.Validator{Jailed: false})
			},
		},
	}

	for _, tc := range testCases {

		providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(
			t, testkeeper.NewInMemKeeperParams(t))

		// Setup expected mock calls
		gomock.InOrder(tc.expectedCalls(ctx, mocks, tc.packetData)...)

		// Setup init chain height and a single valid valset update ID to block height mapping.
		providerKeeper.SetInitChainHeight(ctx, chainId, 5)
		providerKeeper.SetValsetUpdateBlockHeight(ctx, validVscID, 99)

		// Execute method and assert expected mock calls.
		providerKeeper.HandleSlashPacket(ctx, chainId, tc.packetData)
		ctrl.Finish()
	}
}
