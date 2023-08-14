package keeper_test

import (
	"fmt"
	"sort"
	"testing"
	"time"

	clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v7/modules/core/04-channel/types"
	host "github.com/cosmos/ibc-go/v7/modules/core/24-host"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	sdk "github.com/cosmos/cosmos-sdk/types"
	capabilitytypes "github.com/cosmos/cosmos-sdk/x/capability/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	abci "github.com/cometbft/cometbft/abci/types"
	"github.com/cometbft/cometbft/libs/bytes"

	"github.com/cosmos/interchain-security/v3/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/v3/testutil/keeper"
	consumerkeeper "github.com/cosmos/interchain-security/v3/x/ccv/consumer/keeper"
	consumertypes "github.com/cosmos/interchain-security/v3/x/ccv/consumer/types"
	"github.com/cosmos/interchain-security/v3/x/ccv/types"
	ccvtypes "github.com/cosmos/interchain-security/v3/x/ccv/types"
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
	moduleParams := ccvtypes.DefaultParams()
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
	consumerKeeper.SetParams(ctx, ccvtypes.DefaultParams())

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

// TestSendPackets tests the SendPackets method failing
func TestSendPacketsFailure(t *testing.T) {
	// Keeper setup
	consumerKeeper, ctx, ctrl, mocks := testkeeper.GetConsumerKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()
	consumerKeeper.SetProviderChannel(ctx, "consumerCCVChannelID")
	consumerKeeper.SetParams(ctx, ccvtypes.DefaultParams())

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
	consumerKeeper.SetParams(ctx, ccvtypes.DefaultParams())

	// No slash record should exist
	_, found := consumerKeeper.GetSlashRecord(ctx)
	require.False(t, found)
	require.True(t, consumerKeeper.PacketSendingPermitted(ctx))

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

	// First two vsc matured and slash should be sent, 3 total
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

	// Packet sending not permitted
	require.False(t, consumerKeeper.PacketSendingPermitted(ctx))

	// Now delete slash record as would be done by a recv SlashPacketHandledResult
	// then confirm last vsc matured is sent
	consumerKeeper.ClearSlashRecord(ctx)
	consumerKeeper.DeleteHeadOfPendingPackets(ctx)

	// Packet sending permitted
	require.True(t, consumerKeeper.PacketSendingPermitted(ctx))

	gomock.InAnyOrder(
		testkeeper.GetMocksForSendIBCPacket(ctx, mocks, "consumerCCVChannelID", 1),
	)

	consumerKeeper.SendPackets(ctx)
	ctrl.Finish()

	// No packets should be left
	pendingPackets = consumerKeeper.GetPendingPackets(ctx)
	require.Equal(t, 0, len(pendingPackets))
}

// TestOnAcknowledgementPacketError tests application logic for ERROR acknowledgments of sent VSCMatured and Slash packets
// in conjunction with the ibc module's execution of "acknowledgePacket",
// according to https://github.com/cosmos/ibc/tree/main/spec/core/ics-004-channel-and-packet-semantics#processing-acknowledgements
func TestOnAcknowledgementPacketError(t *testing.T) {
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

	slashPacketData := types.NewSlashPacketData(
		abci.Validator{Address: bytes.HexBytes{}, Power: int64(1)}, uint64(1), stakingtypes.Infraction_INFRACTION_DOWNTIME,
	)

	// The type that'd be JSON marshaled and sent over the wire
	consumerPacketData := types.NewConsumerPacketData(
		types.SlashPacket,
		&types.ConsumerPacketData_SlashPacketData{
			SlashPacketData: slashPacketData,
		},
	)

	// AcknowledgePacket is in reference to a packet originally sent from this (consumer) module.
	packet := channeltypes.NewPacket(
		consumerPacketData.GetBytes(),
		1,
		types.ConsumerPortID, // Source port
		channelIDToDestChain, // Source channel
		types.ProviderPortID, // Dest (counter party) port
		channelIDOnDest,      // Dest (counter party) channel
		clienttypes.Height{},
		uint64(time.Now().Add(60*time.Second).UnixNano()),
	)

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

	ack := types.NewErrorAcknowledgementWithLog(ctx, fmt.Errorf("error"))
	err := consumerKeeper.OnAcknowledgementPacket(ctx, packet, ack)
	require.Nil(t, err)
}

// TestOnAcknowledgementPacketResult tests application logic for RESULT acknowledgments of sent VSCMatured and Slash packets
// in conjunction with the ibc module's execution of "acknowledgePacket",
func TestOnAcknowledgementPacketResult(t *testing.T) {
	// Setup
	consumerKeeper, ctx, ctrl, _ := testkeeper.GetConsumerKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	setupSlashBeforeVscMatured(ctx, &consumerKeeper)

	// Slash record found, 2 pending packets, slash is at head of queue
	_, found := consumerKeeper.GetSlashRecord(ctx)
	require.True(t, found)
	pendingPackets := consumerKeeper.GetPendingPackets(ctx)
	require.Len(t, pendingPackets, 2)
	require.Equal(t, types.SlashPacket, pendingPackets[0].Type)

	// v1 result should delete slash record and head of pending packets. Vsc matured remains
	ack := channeltypes.NewResultAcknowledgement(types.V1Result)
	packet := channeltypes.Packet{Data: pendingPackets[0].GetBytes()}
	err := consumerKeeper.OnAcknowledgementPacket(ctx, packet, ack)
	require.Nil(t, err)
	_, found = consumerKeeper.GetSlashRecord(ctx)
	require.False(t, found)
	require.Len(t, consumerKeeper.GetPendingPackets(ctx), 1)
	require.Equal(t, types.VscMaturedPacket, consumerKeeper.GetPendingPackets(ctx)[0].Type)

	// refresh state
	setupSlashBeforeVscMatured(ctx, &consumerKeeper)
	pendingPackets = consumerKeeper.GetPendingPackets(ctx)
	packet = channeltypes.Packet{Data: pendingPackets[0].GetBytes()}

	// Slash packet handled result should delete slash record and head of pending packets
	ack = channeltypes.NewResultAcknowledgement(types.SlashPacketHandledResult)
	err = consumerKeeper.OnAcknowledgementPacket(ctx, packet, ack)
	require.Nil(t, err)
	_, found = consumerKeeper.GetSlashRecord(ctx)
	require.False(t, found)
	require.Len(t, consumerKeeper.GetPendingPackets(ctx), 1)
	require.Equal(t, types.VscMaturedPacket, consumerKeeper.GetPendingPackets(ctx)[0].Type)

	// refresh state
	setupSlashBeforeVscMatured(ctx, &consumerKeeper)
	pendingPackets = consumerKeeper.GetPendingPackets(ctx)
	packet = channeltypes.Packet{Data: pendingPackets[0].GetBytes()}

	slashRecordBefore, found := consumerKeeper.GetSlashRecord(ctx)
	require.True(t, found)
	require.True(t, slashRecordBefore.WaitingOnReply)

	// Slash packet bounced result should update slash record
	ack = channeltypes.NewResultAcknowledgement(types.SlashPacketBouncedResult)
	err = consumerKeeper.OnAcknowledgementPacket(ctx, packet, ack)
	require.Nil(t, err)
	slashRecordAfter, found := consumerKeeper.GetSlashRecord(ctx)
	require.True(t, found)
	require.False(t, slashRecordAfter.WaitingOnReply) // waiting on reply toggled false
	require.Equal(t, slashRecordAfter.SendTime.UnixNano(),
		slashRecordBefore.SendTime.UnixNano()) // send time NOT updated. Bounce result shouldn't affect that
}

func setupSlashBeforeVscMatured(ctx sdk.Context, k *consumerkeeper.Keeper) {
	// clear old state
	k.ClearSlashRecord(ctx)
	k.DeleteAllPendingDataPackets(ctx)

	// Set some related state to test against
	k.SetSlashRecord(ctx, consumertypes.SlashRecord{WaitingOnReply: true, SendTime: time.Now()})
	// Slash packet before VSCMatured packet
	k.AppendPendingPacket(ctx, types.SlashPacket, &types.ConsumerPacketData_SlashPacketData{ // Slash appears first
		SlashPacketData: &types.SlashPacketData{
			Validator:      abci.Validator{},
			ValsetUpdateId: 88,
			Infraction:     stakingtypes.Infraction_INFRACTION_DOWNTIME,
		},
	})
	k.AppendPendingPacket(ctx, types.VscMaturedPacket, &types.ConsumerPacketData_VscMaturedPacketData{
		VscMaturedPacketData: &types.VSCMaturedPacketData{
			ValsetUpdateId: 90,
		},
	})
}

// Regression test for https://github.com/cosmos/interchain-security/issues/1145
func TestSendPacketsDeletion(t *testing.T) {
	// Keeper setup
	consumerKeeper, ctx, ctrl, mocks := testkeeper.GetConsumerKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()
	consumerKeeper.SetProviderChannel(ctx, "consumerCCVChannelID")
	consumerKeeper.SetParams(ctx, ccvtypes.DefaultParams())

	// Queue two pending packets, vsc matured first
	consumerKeeper.AppendPendingPacket(ctx, types.VscMaturedPacket, &types.ConsumerPacketData_VscMaturedPacketData{
		VscMaturedPacketData: &types.VSCMaturedPacketData{
			ValsetUpdateId: 90,
		},
	})
	consumerKeeper.AppendPendingPacket(ctx, types.SlashPacket, &types.ConsumerPacketData_SlashPacketData{ // Slash appears first
		SlashPacketData: &types.SlashPacketData{
			Validator:      abci.Validator{},
			ValsetUpdateId: 88,
			Infraction:     stakingtypes.Infraction_INFRACTION_DOWNTIME,
		},
	})

	// Get mocks for the (first) successful SendPacket call that does NOT return an error
	expectations := testkeeper.GetMocksForSendIBCPacket(ctx, mocks, "consumerCCVChannelID", 1)
	// Append mocks for the (second) failed SendPacket call, which returns an error
	expectations = append(expectations, mocks.MockChannelKeeper.EXPECT().GetChannel(ctx, types.ConsumerPortID,
		"consumerCCVChannelID").Return(channeltypes.Channel{}, false).Times(1))
	gomock.InOrder(expectations...)

	consumerKeeper.SendPackets(ctx)

	// Expect the first successfully sent packet to be popped from queue
	require.Equal(t, 1, len(consumerKeeper.GetPendingPackets(ctx)))

	// Expect the slash packet to remain
	require.Equal(t, types.SlashPacket, consumerKeeper.GetPendingPackets(ctx)[0].Type)
}
