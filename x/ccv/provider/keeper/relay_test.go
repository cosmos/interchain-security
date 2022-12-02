package keeper_test

import (
	"testing"

	"github.com/golang/mock/gomock"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	ibcsimapp "github.com/cosmos/ibc-go/v3/testing/simapp"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	abci "github.com/tendermint/tendermint/abci/types"

	"github.com/stretchr/testify/require"
)

func TestValidateVSCMaturedPacket(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(
		t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	packet := channeltypes.Packet{DestinationChannel: "channel-7"}
	data := ccv.VSCMaturedPacketData{}

	// validate method panics if there is no established ccv channel
	// with channel ID specified in packet.
	require.Panics(t, func() {
		providerKeeper.ValidateVSCMaturedPacket(ctx, packet, data)
	})

	// Pseudo setup ccv channel for channel ID specified in packet.
	providerKeeper.SetChannelToChain(ctx, "channel-7", "consumer-chain-id")

	// validate method now passes.
	err := providerKeeper.ValidateVSCMaturedPacket(ctx, packet, data)
	require.NoError(t, err)
}

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
		pk.AppendPendingPackets(ctx, chainID, tc.packets...)

		pk.QueueVSCPackets(ctx)
		pending := pk.GetPendingPackets(ctx, chainID)
		require.Len(t, pending, tc.expectedQueueSize, "pending vsc queue mismatch (%v != %v) in case: '%s'", tc.expectedQueueSize, len(pending), tc.name)

		// next valset update ID -> default value in tests is 0
		// each call to QueueValidatorUpdates will increment the ValidatorUpdateID
		valUpdateID := pk.GetValidatorSetUpdateId(ctx)
		require.Equal(t, tc.expectNextValsetUpdateId, valUpdateID, "valUpdateID (%v != %v) mismatch in case: '%s'", tc.expectNextValsetUpdateId, valUpdateID, tc.name)
	}
}

// TestValidateSlashPacket tests ValidateSlashPacket.
func TestValidateSlashPacket(t *testing.T) {

	validVscID := uint64(98)

	testCases := []struct {
		name       string
		packetData ccv.SlashPacketData
		expectErr  bool
	}{
		{"no block height found for given vscID",
			ccv.SlashPacketData{ValsetUpdateId: 61},
			true},
		{"non-set infraction type",
			ccv.SlashPacketData{ValsetUpdateId: validVscID},
			true},
		{"invalid infraction type",
			ccv.SlashPacketData{ValsetUpdateId: validVscID, Infraction: stakingtypes.MaxMonikerLength},
			true},
		{"valid double sign packet with non-zero vscID",
			ccv.SlashPacketData{ValsetUpdateId: validVscID, Infraction: stakingtypes.DoubleSign},
			false},
		{"valid downtime packet with non-zero vscID",
			ccv.SlashPacketData{ValsetUpdateId: validVscID, Infraction: stakingtypes.Downtime},
			false},
		{"valid double sign packet with zero vscID",
			ccv.SlashPacketData{ValsetUpdateId: 0, Infraction: stakingtypes.DoubleSign},
			false},
		{"valid downtime packet with zero vscID",
			ccv.SlashPacketData{ValsetUpdateId: 0, Infraction: stakingtypes.Downtime},
			false},
	}

	for _, tc := range testCases {
		providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(
			t, testkeeper.NewInMemKeeperParams(t))
		defer ctrl.Finish()

		packet := channeltypes.Packet{DestinationChannel: "channel-9"}

		// validate method panics if there is no established ccv channel
		// with channel ID specified in packet.
		require.Panics(t, func() {
			providerKeeper.ValidateSlashPacket(ctx, packet, tc.packetData)
		})

		// Pseudo setup ccv channel for channel ID specified in packet.
		providerKeeper.SetChannelToChain(ctx, "channel-9", "consumer-chain-id")

		// Setup init chain height for consumer (allowing 0 vscID to be valid).
		providerKeeper.SetInitChainHeight(ctx, "consumer-chain-id", uint64(89))

		// Setup valset update ID to block height mapping using var instantiated above.
		providerKeeper.SetValsetUpdateBlockHeight(ctx, validVscID, uint64(100))

		// Test error behavior as specified in tc.
		err := providerKeeper.ValidateSlashPacket(ctx, packet, tc.packetData)
		if tc.expectErr {
			require.Error(t, err, "expected error in case: '%s'", tc.name)
		} else {
			require.NoError(t, err, "unexpected error in case: '%s'", tc.name)
		}
	}
}
