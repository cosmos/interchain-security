package keeper_test

import (
	"fmt"
	"sort"
	"testing"
	"time"

	abci "github.com/cometbft/cometbft/abci/types"
	"github.com/cometbft/cometbft/libs/bytes"
	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	capabilitytypes "github.com/cosmos/cosmos-sdk/x/capability/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v7/modules/core/04-channel/types"
	host "github.com/cosmos/ibc-go/v7/modules/core/24-host"

	"github.com/cosmos/interchain-security/v3/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/v3/testutil/keeper"
	consumertypes "github.com/cosmos/interchain-security/v3/x/ccv/consumer/types"
	"github.com/cosmos/interchain-security/v3/x/ccv/types"

	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"
)

// TestOnRecvVSCPacket tests the behavior of OnRecvVSCPacket over various packet scenarios
func TestOnRecvVSCPacket(t *testing.T) {
	consumerCCVChannelID := "consumerCCVChannelID"
	providerCCVChannelID := "providerCCVChannelID"

	pk1, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
	require.NoError(t, err)
	pk2, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
	require.NoError(t, err)
	pk3, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
	require.NoError(t, err)

	changes1 := []abci.ValidatorUpdate{
		{
			PubKey: pk1,
			Power:  30,
		},
		{
			PubKey: pk2,
			Power:  20,
		},
	}

	changes2 := []abci.ValidatorUpdate{
		{
			PubKey: pk2,
			Power:  40,
		},
		{
			PubKey: pk3,
			Power:  10,
		},
	}

	pd := types.NewValidatorSetChangePacketData(
		changes1,
		1,
		nil,
	)

	pd2 := types.NewValidatorSetChangePacketData(
		changes2,
		2,
		nil,
	)

	testCases := []struct {
		name                   string
		packet                 channeltypes.Packet
		newChanges             types.ValidatorSetChangePacketData
		expectedPendingChanges types.ValidatorSetChangePacketData
	}{
		{
			"success on first packet",
			channeltypes.NewPacket(pd.GetBytes(), 1, types.ProviderPortID, providerCCVChannelID, types.ConsumerPortID, consumerCCVChannelID,
				clienttypes.NewHeight(1, 0), 0),
			types.ValidatorSetChangePacketData{ValidatorUpdates: changes1},
			types.ValidatorSetChangePacketData{ValidatorUpdates: changes1},
		},
		{
			"success on subsequent packet",
			channeltypes.NewPacket(pd.GetBytes(), 2, types.ProviderPortID, providerCCVChannelID, types.ConsumerPortID, consumerCCVChannelID,
				clienttypes.NewHeight(1, 0), 0),
			types.ValidatorSetChangePacketData{ValidatorUpdates: changes1},
			types.ValidatorSetChangePacketData{ValidatorUpdates: changes1},
		},
		{
			"success on packet with more changes",
			channeltypes.NewPacket(pd2.GetBytes(), 3, types.ProviderPortID, providerCCVChannelID, types.ConsumerPortID, consumerCCVChannelID,
				clienttypes.NewHeight(1, 0), 0),
			types.ValidatorSetChangePacketData{ValidatorUpdates: changes2},
			types.ValidatorSetChangePacketData{ValidatorUpdates: []abci.ValidatorUpdate{
				{
					PubKey: pk1,
					Power:  30,
				},
				{
					PubKey: pk2,
					Power:  40,
				},
				{
					PubKey: pk3,
					Power:  10,
				},
			}},
		},
	}

	consumerKeeper, ctx, ctrl, _ := testkeeper.GetConsumerKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// Set channel to provider, still in context of consumer chain
	consumerKeeper.SetProviderChannel(ctx, consumerCCVChannelID)

	// Set module params with custom unbonding period
	moduleParams := consumertypes.DefaultParams()
	moduleParams.UnbondingPeriod = 100 * time.Hour
	consumerKeeper.SetParams(ctx, moduleParams)

	for _, tc := range testCases {
		ack := consumerKeeper.OnRecvVSCPacket(ctx, tc.packet, tc.newChanges)

		require.NotNil(t, ack, "invalid test case: %s did not return ack", tc.name)
		require.True(t, ack.Success(), "invalid test case: %s did not return a Success Acknowledgment", tc.name)
		providerChannel, ok := consumerKeeper.GetProviderChannel(ctx)
		require.True(t, ok)
		require.Equal(t, tc.packet.DestinationChannel, providerChannel,
			"provider channel is not destination channel on successful receive for valid test case: %s", tc.name)

		// Check that pending changes are accumulated and stored correctly
		actualPendingChanges, ok := consumerKeeper.GetPendingChanges(ctx)
		require.True(t, ok)
		// Sort to avoid dumb inequalities
		sort.SliceStable(actualPendingChanges.ValidatorUpdates, func(i, j int) bool {
			return actualPendingChanges.ValidatorUpdates[i].PubKey.Compare(actualPendingChanges.ValidatorUpdates[j].PubKey) == -1
		})
		sort.SliceStable(tc.expectedPendingChanges.ValidatorUpdates, func(i, j int) bool {
			return tc.expectedPendingChanges.ValidatorUpdates[i].PubKey.Compare(tc.expectedPendingChanges.ValidatorUpdates[j].PubKey) == -1
		})
		require.Equal(t, tc.expectedPendingChanges, *actualPendingChanges, "pending changes not equal to expected changes after successful packet receive. case: %s", tc.name)

		expectedTime := ctx.BlockTime().Add(consumerKeeper.GetUnbondingPeriod(ctx))
		require.True(
			t,
			consumerKeeper.PacketMaturityTimeExists(ctx, tc.newChanges.ValsetUpdateId, expectedTime),
			"no packet maturity time for case: %s", tc.name,
		)
	}
}

// TestOnRecvVSCPacketDuplicateUpdates tests that the consumer can correctly handle a single VSC packet
// with duplicate valUpdates for the same pub key.
//
// Note: This scenario shouldn't usually happen, ie. the provider shouldn't send duplicate val updates
// for the same pub key. But it's useful to guard against.
func TestOnRecvVSCPacketDuplicateUpdates(t *testing.T) {
	// Arbitrary channel IDs
	consumerCCVChannelID := "consumerCCVChannelID"
	providerCCVChannelID := "providerCCVChannelID"

	// Keeper setup
	consumerKeeper, ctx, ctrl, _ := testkeeper.GetConsumerKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()
	consumerKeeper.SetProviderChannel(ctx, consumerCCVChannelID)
	consumerKeeper.SetParams(ctx, consumertypes.DefaultParams())

	// Construct packet/data with duplicate val updates for the same pub key
	cId := crypto.NewCryptoIdentityFromIntSeed(43278947)
	valUpdates := []abci.ValidatorUpdate{
		{
			PubKey: cId.TMProtoCryptoPublicKey(),
			Power:  0,
		},
		{
			PubKey: cId.TMProtoCryptoPublicKey(),
			Power:  473289,
		},
	}
	vscData := types.NewValidatorSetChangePacketData(
		valUpdates,
		1,
		nil,
	)
	packet := channeltypes.NewPacket(vscData.GetBytes(), 2, types.ProviderPortID,
		providerCCVChannelID, types.ConsumerPortID, consumerCCVChannelID, clienttypes.NewHeight(1, 0), 0)

	// Confirm no pending changes exist before OnRecvVSCPacket
	_, ok := consumerKeeper.GetPendingChanges(ctx)
	require.False(t, ok)

	// Execute OnRecvVSCPacket
	ack := consumerKeeper.OnRecvVSCPacket(ctx, packet, vscData)
	require.NotNil(t, ack)
	require.True(t, ack.Success())

	// Confirm pending changes are queued by OnRecvVSCPacket
	gotPendingChanges, ok := consumerKeeper.GetPendingChanges(ctx)
	require.True(t, ok)

	// Confirm that only the latest update is kept, duplicate update is discarded
	require.Equal(t, 1, len(gotPendingChanges.ValidatorUpdates))
	require.Equal(t, valUpdates[1], gotPendingChanges.ValidatorUpdates[0]) // Only latest update should be kept
}

// TestOnAcknowledgementPacket tests application logic for acknowledgments of sent VSCMatured and Slash packets
// in conjunction with the ibc module's execution of "acknowledgePacket",
// according to https://github.com/cosmos/ibc/tree/main/spec/core/ics-004-channel-and-packet-semantics#processing-acknowledgements
func TestOnAcknowledgementPacket(t *testing.T) {
	// Channel ID to some dest chain that's not the established provider
	channelIDToDestChain := "channelIDToDestChain"

	// Channel ID to established provider
	channelIDToProvider := "channelIDToProvider"

	// Channel ID on destination (counter party) chain
	channelIDOnDest := "ChannelIDOnDest"

	// Instantiate in-mem keeper with mocks
	ctrl := gomock.NewController(t)
	defer ctrl.Finish()
	keeperParams := testkeeper.NewInMemKeeperParams(t)
	mocks := testkeeper.NewMockedKeepers(ctrl)
	consumerKeeper := testkeeper.NewInMemConsumerKeeper(keeperParams, mocks)
	ctx := keeperParams.Ctx

	// Set an established provider channel for later in test
	consumerKeeper.SetProviderChannel(ctx, channelIDToProvider)

	packetData := types.NewSlashPacketData(
		abci.Validator{Address: bytes.HexBytes{}, Power: int64(1)}, uint64(1), stakingtypes.Infraction_INFRACTION_DOWNTIME,
	)

	// AcknowledgePacket is in reference to a packet originally sent from this (consumer) module.
	packet := channeltypes.NewPacket(
		packetData.GetBytes(),
		1,
		types.ConsumerPortID, // Source port
		channelIDToDestChain, // Source channel
		types.ProviderPortID, // Dest (counter party) port
		channelIDOnDest,      // Dest (counter party) channel
		clienttypes.Height{},
		uint64(time.Now().Add(60*time.Second).UnixNano()),
	)

	ack := channeltypes.NewResultAcknowledgement([]byte{1})

	// expect no error returned from OnAcknowledgementPacket, no input error with ack
	err := consumerKeeper.OnAcknowledgementPacket(ctx, packet, ack)
	require.Nil(t, err)

	// Still expect no error returned from OnAcknowledgementPacket,
	// but the input error ack will be handled with appropriate ChanCloseInit calls
	dummyCap := &capabilitytypes.Capability{}
	gomock.InOrder(

		mocks.MockScopedKeeper.EXPECT().GetCapability(
			ctx, host.ChannelCapabilityPath(types.ConsumerPortID, channelIDToDestChain),
		).Return(dummyCap, true).Times(1),
		// Due to input error ack, ChanCloseInit is called on channel to destination chain
		mocks.MockChannelKeeper.EXPECT().ChanCloseInit(
			ctx, types.ConsumerPortID, channelIDToDestChain, dummyCap,
		).Return(nil).Times(1),

		mocks.MockScopedKeeper.EXPECT().GetCapability(
			ctx, host.ChannelCapabilityPath(types.ConsumerPortID, channelIDToProvider),
		).Return(dummyCap, true).Times(1),
		// Due to input error ack and existence of established channel to provider,
		// ChanCloseInit is called on channel to provider
		mocks.MockChannelKeeper.EXPECT().ChanCloseInit(
			ctx, types.ConsumerPortID, channelIDToProvider, dummyCap,
		).Return(nil).Times(1),
	)

	ack = types.NewErrorAcknowledgementWithLog(ctx, fmt.Errorf("error"))
	err = consumerKeeper.OnAcknowledgementPacket(ctx, packet, ack)
	require.Nil(t, err)
}

// TestSendPackets tests the SendPackets method failing
func TestSendPacketsFailure(t *testing.T) {
	// Keeper setup
	consumerKeeper, ctx, ctrl, mocks := testkeeper.GetConsumerKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()
	consumerKeeper.SetProviderChannel(ctx, "consumerCCVChannelID")
	consumerKeeper.SetParams(ctx, consumertypes.DefaultParams())

	// Set some pending packets
	consumerKeeper.AppendPendingPacket(ctx, types.VscMaturedPacket, &types.ConsumerPacketData_VscMaturedPacketData{})
	consumerKeeper.AppendPendingPacket(ctx, types.SlashPacket, &types.ConsumerPacketData_SlashPacketData{})
	consumerKeeper.AppendPendingPacket(ctx, types.VscMaturedPacket, &types.ConsumerPacketData_VscMaturedPacketData{})

	// Mock the channel keeper to return an error
	gomock.InOrder(
		mocks.MockChannelKeeper.EXPECT().GetChannel(ctx, types.ConsumerPortID,
			"consumerCCVChannelID").Return(channeltypes.Channel{}, false).Times(1),
	)

	// No panic should occur, pending packets should not be cleared
	consumerKeeper.SendPackets(ctx)
	require.Equal(t, 3, len(consumerKeeper.GetPendingPackets(ctx)))
}

func TestSendPackets(t *testing.T) {
	// Keeper setup
	consumerKeeper, ctx, ctrl, mocks := testkeeper.GetConsumerKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	consumerKeeper.SetProviderChannel(ctx, "consumerCCVChannelID")
	consumerKeeper.SetParams(ctx, consumertypes.DefaultParams())

	// No slash record should exist
	_, found := consumerKeeper.GetSlashRecord(ctx)
	require.False(t, found)

	// Queue up two vsc matured, followed by slash, followed by vsc matured
	consumerKeeper.AppendPendingPacket(ctx, types.VscMaturedPacket, &types.ConsumerPacketData_VscMaturedPacketData{
		VscMaturedPacketData: &types.VSCMaturedPacketData{
			ValsetUpdateId: 77,
		},
	})
	consumerKeeper.AppendPendingPacket(ctx, types.VscMaturedPacket, &types.ConsumerPacketData_VscMaturedPacketData{
		VscMaturedPacketData: &types.VSCMaturedPacketData{
			ValsetUpdateId: 90,
		},
	})
	consumerKeeper.AppendPendingPacket(ctx, types.SlashPacket, &types.ConsumerPacketData_SlashPacketData{
		SlashPacketData: &types.SlashPacketData{
			Validator:      abci.Validator{},
			ValsetUpdateId: 88,
			Infraction:     stakingtypes.Infraction_INFRACTION_DOWNTIME,
		},
	})
	consumerKeeper.AppendPendingPacket(ctx, types.VscMaturedPacket, &types.ConsumerPacketData_VscMaturedPacketData{
		VscMaturedPacketData: &types.VSCMaturedPacketData{
			ValsetUpdateId: 99,
		},
	})

	// First vsc matured and slash should be sent, 3 total
	gomock.InAnyOrder(
		testkeeper.GetMocksForSendIBCPacket(ctx, mocks, "consumerCCVChannelID", 3),
	)
	consumerKeeper.SendPackets(ctx)
	ctrl.Finish()

	// First two packets should be deleted, slash should be at head of queue
	pendingPackets := consumerKeeper.GetPendingPackets(ctx)
	require.Equal(t, 2, len(pendingPackets))
	require.Equal(t, types.SlashPacket, pendingPackets[0].Type)
	require.Equal(t, types.VscMaturedPacket, pendingPackets[1].Type)

	// Now delete slash record as would be done by a recv SlashPacketHandledResult
	// then confirm last vsc matured is sent
	consumerKeeper.ClearSlashRecord(ctx)
	consumerKeeper.DeleteHeadOfPendingPackets(ctx)

	gomock.InAnyOrder(
		testkeeper.GetMocksForSendIBCPacket(ctx, mocks, "consumerCCVChannelID", 1),
	)

	consumerKeeper.SendPackets(ctx)
	ctrl.Finish()

	// No packets should be left
	pendingPackets = consumerKeeper.GetPendingPackets(ctx)
	require.Equal(t, 0, len(pendingPackets))
}
