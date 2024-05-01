package keeper_test

import (
	"bytes"
	"sort"
	"testing"
	"time"

	conntypes "github.com/cosmos/ibc-go/v7/modules/core/03-connection/types"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	abci "github.com/cometbft/cometbft/abci/types"

	"github.com/cosmos/interchain-security/v5/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/v5/testutil/keeper"
	"github.com/cosmos/interchain-security/v5/x/ccv/consumer/types"
	ccv "github.com/cosmos/interchain-security/v5/x/ccv/types"
)

// TestProviderClientID tests getter and setter functionality for the client ID stored on consumer keeper
func TestProviderClientID(t *testing.T) {
	consumerKeeper, ctx, ctrl, _ := testkeeper.GetConsumerKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	_, ok := consumerKeeper.GetProviderClientID(ctx)
	require.False(t, ok)
	consumerKeeper.SetProviderClientID(ctx, "someClientID")
	clientID, ok := consumerKeeper.GetProviderClientID(ctx)
	require.True(t, ok)
	require.Equal(t, "someClientID", clientID)
}

// TestProviderChannel tests getter and setter functionality for the channel ID stored on consumer keeper
func TestProviderChannel(t *testing.T) {
	consumerKeeper, ctx, ctrl, _ := testkeeper.GetConsumerKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	_, ok := consumerKeeper.GetProviderChannel(ctx)
	require.False(t, ok)
	consumerKeeper.SetProviderChannel(ctx, "channelID")
	channelID, ok := consumerKeeper.GetProviderChannel(ctx)
	require.True(t, ok)
	require.Equal(t, "channelID", channelID)
}

// TestPendingChanges tests getter, setter, and delete functionality for pending VSCs on a consumer chain
func TestPendingChanges(t *testing.T) {
	pk1, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
	require.NoError(t, err)
	pk2, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
	require.NoError(t, err)

	pd := ccv.NewValidatorSetChangePacketData(
		[]abci.ValidatorUpdate{
			{
				PubKey: pk1,
				Power:  30,
			},
			{
				PubKey: pk2,
				Power:  20,
			},
		},
		1,
		nil,
	)

	consumerKeeper, ctx, ctrl, _ := testkeeper.GetConsumerKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerKeeper.SetPendingChanges(ctx, pd)
	gotPd, ok := consumerKeeper.GetPendingChanges(ctx)
	require.True(t, ok)
	require.Equal(t, &pd, gotPd, "packet data in store does not equal packet data set")
	consumerKeeper.DeletePendingChanges(ctx)
	gotPd, ok = consumerKeeper.GetPendingChanges(ctx)
	require.False(t, ok)
	require.Nil(t, gotPd, "got non-nil pending changes after Delete")
}

// TestLastSovereignHeight tests the getter and setter for the ccv init genesis height
func TestInitGenesisHeight(t *testing.T) {
	consumerKeeper, ctx, ctrl, _ := testkeeper.GetConsumerKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// Panics without setter
	require.Panics(t, func() { consumerKeeper.GetInitGenesisHeight(ctx) })

	// Set/get the height being 10
	consumerKeeper.SetInitGenesisHeight(ctx, 10)
	require.Equal(t, int64(10), consumerKeeper.GetInitGenesisHeight(ctx))

	// Set/get the height being 43234426
	consumerKeeper.SetInitGenesisHeight(ctx, 43234426)
	require.Equal(t, int64(43234426), consumerKeeper.GetInitGenesisHeight(ctx))
}

// TestPreCCV tests the getter, setter and deletion methods for the pre-CCV state flag
func TestPreCCV(t *testing.T) {
	consumerKeeper, ctx, ctrl, _ := testkeeper.GetConsumerKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// Default value is false without any setter
	require.False(t, consumerKeeper.IsPreCCV(ctx))

	// Set/get the pre-CCV state to true
	consumerKeeper.SetPreCCVTrue(ctx)
	require.True(t, consumerKeeper.IsPreCCV(ctx))

	// Delete the pre-CCV state, setting it to false
	consumerKeeper.DeletePreCCV(ctx)
	require.False(t, consumerKeeper.IsPreCCV(ctx))
}

// TestInitialValSet tests the getter and setter methods for storing the initial validator set for a consumer
func TestInitialValSet(t *testing.T) {
	consumerKeeper, ctx, ctrl, _ := testkeeper.GetConsumerKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// Default value is empty val update list
	require.Empty(t, consumerKeeper.GetInitialValSet(ctx))

	// Set/get the initial validator set
	cId1 := crypto.NewCryptoIdentityFromIntSeed(7896)
	cId2 := crypto.NewCryptoIdentityFromIntSeed(7897)
	cId3 := crypto.NewCryptoIdentityFromIntSeed(7898)
	valUpdates := []abci.ValidatorUpdate{
		{
			PubKey: cId1.TMProtoCryptoPublicKey(),
			Power:  1097,
		},
		{
			PubKey: cId2.TMProtoCryptoPublicKey(),
			Power:  19068,
		},
		{
			PubKey: cId3.TMProtoCryptoPublicKey(),
			Power:  10978554,
		},
	}

	consumerKeeper.SetInitialValSet(ctx, valUpdates)
	require.Equal(t, []abci.ValidatorUpdate{
		{
			PubKey: cId1.TMProtoCryptoPublicKey(),
			Power:  1097,
		},
		{
			PubKey: cId2.TMProtoCryptoPublicKey(),
			Power:  19068,
		},
		{
			PubKey: cId3.TMProtoCryptoPublicKey(),
			Power:  10978554,
		},
	}, consumerKeeper.GetInitialValSet(ctx))
}

// TestGetLastSovereignValidators tests the getter method for getting the last valset
// from the standalone staking keeper
func TestGetLastSovereignValidators(t *testing.T) {
	ck, ctx, ctrl, mocks := testkeeper.GetConsumerKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// Should panic if pre-CCV is true but staking keeper is not set
	ck.SetPreCCVTrue(ctx)
	require.Panics(t, func() { ck.GetLastStandaloneValidators(ctx) })

	// Should panic if staking keeper is set but pre-CCV is false
	ck.SetStandaloneStakingKeeper(mocks.MockStakingKeeper)
	ck.DeletePreCCV(ctx)
	require.False(t, ck.IsPreCCV(ctx))
	require.Panics(t, func() { ck.GetLastStandaloneValidators(ctx) })

	// Set the pre-CCV state to true and get the last standalone validators from mock
	ck.SetPreCCVTrue(ctx)
	require.True(t, ck.IsPreCCV(ctx))
	cId1 := crypto.NewCryptoIdentityFromIntSeed(11)
	val := cId1.SDKStakingValidator()
	val.Description.Moniker = "sanity check this is the correctly serialized val"
	gomock.InOrder(
		mocks.MockStakingKeeper.EXPECT().GetLastValidators(ctx).Return([]stakingtypes.Validator{
			val,
		}),
	)
	lastSovVals := ck.GetLastStandaloneValidators(ctx)
	require.Equal(t, []stakingtypes.Validator{val}, lastSovVals)
	require.Equal(t, "sanity check this is the correctly serialized val",
		lastSovVals[0].Description.Moniker)
}

// TestPacketMaturityTime tests getter, setter, and iterator functionality for the packet maturity time of a received VSC packet
func TestPacketMaturityTime(t *testing.T) {
	ck, ctx, ctrl, _ := testkeeper.GetConsumerKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	now := time.Now().UTC()
	packets := []types.MaturingVSCPacket{
		{
			VscId:        2,
			MaturityTime: now,
		},
		{
			VscId:        1,
			MaturityTime: now.Add(-time.Hour),
		},
		{
			VscId:        5,
			MaturityTime: now.Add(-2 * time.Hour),
		},
		{
			VscId:        6,
			MaturityTime: now.Add(time.Hour),
		},
	}
	// sort by MaturityTime and not by VscId
	expectedGetAllOrder := []types.MaturingVSCPacket{packets[2], packets[1], packets[0], packets[3]}
	// only packets with MaturityTime before or equal to now
	expectedGetElapsedOrder := []types.MaturingVSCPacket{packets[2], packets[1], packets[0]}

	// test SetPacketMaturityTime
	for _, packet := range packets {
		ck.SetPacketMaturityTime(ctx, packet.VscId, packet.MaturityTime)
	}

	// test PacketMaturityTimeExists
	for _, packet := range packets {
		require.True(t, ck.PacketMaturityTimeExists(ctx, packet.VscId, packet.MaturityTime))
	}

	// test GetAllPacketMaturityTimes
	maturingVSCPackets := ck.GetAllPacketMaturityTimes(ctx)
	require.Len(t, maturingVSCPackets, len(packets))
	require.Equal(t, expectedGetAllOrder, maturingVSCPackets)

	// test GetElapsedPacketMaturityTimes
	elapsedMaturingVSCPackets := ck.GetElapsedPacketMaturityTimes(ctx.WithBlockTime(now))
	require.Equal(t, expectedGetElapsedOrder, elapsedMaturingVSCPackets)

	// test DeletePacketMaturityTimes
	ck.DeletePacketMaturityTimes(ctx, packets[0].VscId, packets[0].MaturityTime)
	require.False(t, ck.PacketMaturityTimeExists(ctx, packets[0].VscId, packets[0].MaturityTime))
}

// TestCrossChainValidator tests the getter, setter, and deletion method for cross chain validator records
func TestCrossChainValidator(t *testing.T) {
	keeperParams := testkeeper.NewInMemKeeperParams(t)
	consumerKeeper, ctx, ctrl, _ := testkeeper.GetConsumerKeeperAndCtx(t, keeperParams)
	defer ctrl.Finish()

	// should return false
	_, found := consumerKeeper.GetCCValidator(ctx, ed25519.GenPrivKey().PubKey().Address())
	require.False(t, found)

	// Obtain derived private key
	privKey := ed25519.GenPrivKey()

	// Set cross chain validator
	ccVal, err := types.NewCCValidator(privKey.PubKey().Address(), 1000, privKey.PubKey())
	require.NoError(t, err)
	consumerKeeper.SetCCValidator(ctx, ccVal)

	gotCCVal, found := consumerKeeper.GetCCValidator(ctx, ccVal.Address)
	require.True(t, found)

	// verify the returned validator values
	require.EqualValues(t, ccVal, gotCCVal)

	// expect to return the same consensus pubkey
	pk, err := ccVal.ConsPubKey()
	require.NoError(t, err)
	gotPK, err := gotCCVal.ConsPubKey()
	require.NoError(t, err)
	require.Equal(t, pk, gotPK)

	// delete validator
	consumerKeeper.DeleteCCValidator(ctx, ccVal.Address)

	// should return false
	_, found = consumerKeeper.GetCCValidator(ctx, ccVal.Address)
	require.False(t, found)
}

// TestGetAllCCValidator tests GetAllCCValidator behaviour correctness
func TestGetAllCCValidator(t *testing.T) {
	keeperParams := testkeeper.NewInMemKeeperParams(t)
	ck, ctx, ctrl, _ := testkeeper.GetConsumerKeeperAndCtx(t, keeperParams)
	defer ctrl.Finish()

	numValidators := 4
	validators := []types.CrossChainValidator{}
	for i := 0; i < numValidators; i++ {
		validators = append(validators, testkeeper.GetNewCrossChainValidator(t))
	}
	// sorting by CrossChainValidator.Address
	expectedGetAllOrder := validators
	sort.Slice(expectedGetAllOrder, func(i, j int) bool {
		return bytes.Compare(expectedGetAllOrder[i].Address, expectedGetAllOrder[j].Address) == -1
	})

	for _, val := range validators {
		ck.SetCCValidator(ctx, val)
	}

	// iterate and check all results are returned in the expected order
	result := ck.GetAllCCValidator(ctx)
	require.Len(t, result, len(validators))
	require.Equal(t, result, expectedGetAllOrder)
}

func TestPendingPackets(t *testing.T) {
	consumerKeeper, ctx, ctrl, _ := testkeeper.GetConsumerKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// Instantiate some expected packet data
	packetData := []ccv.ConsumerPacketData{
		{
			Type: ccv.VscMaturedPacket,
			Data: &ccv.ConsumerPacketData_VscMaturedPacketData{
				VscMaturedPacketData: ccv.NewVSCMaturedPacketData(1),
			},
		},
		{
			Type: ccv.VscMaturedPacket,
			Data: &ccv.ConsumerPacketData_VscMaturedPacketData{
				VscMaturedPacketData: ccv.NewVSCMaturedPacketData(2),
			},
		},
		{
			Type: ccv.SlashPacket,
			Data: &ccv.ConsumerPacketData_SlashPacketData{
				SlashPacketData: ccv.NewSlashPacketData(
					abci.Validator{Address: ed25519.GenPrivKey().PubKey().Address(), Power: int64(0)},
					3,
					stakingtypes.Infraction_INFRACTION_DOUBLE_SIGN,
				),
			},
		},
		{
			Type: ccv.VscMaturedPacket,
			Data: &ccv.ConsumerPacketData_VscMaturedPacketData{
				VscMaturedPacketData: ccv.NewVSCMaturedPacketData(3),
			},
		},
	}

	// Append all packets to the queue
	for _, data := range packetData {
		consumerKeeper.AppendPendingPacket(ctx, data.Type, data.Data)
	}
	storedPacketData := consumerKeeper.GetPendingPackets(ctx)
	require.NotEmpty(t, storedPacketData)
	require.Equal(t, packetData, storedPacketData)

	slashPacket := ccv.NewSlashPacketData(
		abci.Validator{
			Address: ed25519.GenPrivKey().PubKey().Address(),
			Power:   int64(2),
		},
		uint64(4),
		stakingtypes.Infraction_INFRACTION_DOWNTIME,
	)
	// Append slash packet to expected packet data
	packetData = append(packetData, ccv.ConsumerPacketData{
		Type: ccv.SlashPacket,
		Data: &ccv.ConsumerPacketData_SlashPacketData{
			SlashPacketData: slashPacket,
		},
	})

	toAppend := packetData[len(packetData)-1]
	consumerKeeper.AppendPendingPacket(ctx, toAppend.Type, toAppend.Data)
	storedPacketData = consumerKeeper.GetPendingPackets(ctx)
	require.NotEmpty(t, storedPacketData)
	require.Equal(t, packetData, storedPacketData)

	vscMaturedPacket := ccv.NewVSCMaturedPacketData(4)
	packetData = append(packetData, ccv.ConsumerPacketData{
		Type: ccv.VscMaturedPacket,
		Data: &ccv.ConsumerPacketData_VscMaturedPacketData{
			VscMaturedPacketData: vscMaturedPacket,
		},
	})
	toAppend = packetData[len(packetData)-1]
	consumerKeeper.AppendPendingPacket(ctx, toAppend.Type, toAppend.Data)

	storedPacketData = consumerKeeper.GetPendingPackets(ctx)
	require.NotEmpty(t, storedPacketData)
	require.Equal(t, packetData, storedPacketData)

	// Delete packet with idx 5 (final index)
	consumerKeeper.DeletePendingDataPackets(ctx, 5)
	storedPacketData = consumerKeeper.GetPendingPackets(ctx)
	require.Equal(t, packetData[:len(packetData)-1], storedPacketData)
	pendingPacketsWithIdx := consumerKeeper.GetAllPendingPacketsWithIdx(ctx)
	require.Equal(t, uint64(4), pendingPacketsWithIdx[len(pendingPacketsWithIdx)-1].Idx) // final element should have idx 4

	// Delete packet with idx 0 (first index)
	consumerKeeper.DeletePendingDataPackets(ctx, 0)
	storedPacketData = consumerKeeper.GetPendingPackets(ctx)
	require.Equal(t, packetData[1:len(packetData)-1], storedPacketData)
	pendingPacketsWithIdx = consumerKeeper.GetAllPendingPacketsWithIdx(ctx)
	require.Equal(t, uint64(1), pendingPacketsWithIdx[0].Idx) // first element should have idx 1

	// Delete all packets
	consumerKeeper.DeleteAllPendingDataPackets(ctx)
	storedPacketData = consumerKeeper.GetPendingPackets(ctx)
	require.Empty(t, storedPacketData)
	require.Empty(t, consumerKeeper.GetAllPendingPacketsWithIdx(ctx))
}

// TestVerifyProviderChain tests the VerifyProviderChain method for the consumer keeper
func TestVerifyProviderChain(t *testing.T) {
	testCases := []struct {
		name string
		// State-mutating setup specific to this test case
		mockSetup      func(sdk.Context, testkeeper.MockedKeepers)
		connectionHops []string
		expError       bool
	}{
		{
			name: "success",
			mockSetup: func(ctx sdk.Context, mocks testkeeper.MockedKeepers) {
				gomock.InOrder(
					mocks.MockConnectionKeeper.EXPECT().GetConnection(
						ctx, "connectionID",
					).Return(conntypes.ConnectionEnd{ClientId: "clientID"}, true).Times(1),
				)
			},
			connectionHops: []string{"connectionID"},
			expError:       false,
		},
		{
			name: "connection hops is not length 1",
			mockSetup: func(ctx sdk.Context, mocks testkeeper.MockedKeepers) {
				// Expect no calls to GetConnection(), VerifyProviderChain will return from first step.
				gomock.InAnyOrder(
					mocks.MockConnectionKeeper.EXPECT().GetConnection(gomock.Any(), gomock.Any()).Times(0),
				)
			},
			connectionHops: []string{"connectionID", "otherConnID"},
			expError:       true,
		},
		{
			name: "connection does not exist",
			mockSetup: func(ctx sdk.Context, mocks testkeeper.MockedKeepers) {
				gomock.InOrder(
					mocks.MockConnectionKeeper.EXPECT().GetConnection(
						ctx, "connectionID").Return(conntypes.ConnectionEnd{},
						false, // Found is returned as false
					).Times(1),
				)
			},
			connectionHops: []string{"connectionID"},
			expError:       true,
		},
		{
			name: "found clientID does not match expectation",
			mockSetup: func(ctx sdk.Context, mocks testkeeper.MockedKeepers) {
				gomock.InOrder(
					mocks.MockConnectionKeeper.EXPECT().GetConnection(
						ctx, "connectionID").Return(
						conntypes.ConnectionEnd{ClientId: "unexpectedClientID"}, true,
					).Times(1),
				)
			},
			connectionHops: []string{"connectionID"},
			expError:       true,
		},
	}

	for _, tc := range testCases {

		keeperParams := testkeeper.NewInMemKeeperParams(t)
		consumerKeeper, ctx, ctrl, mocks := testkeeper.GetConsumerKeeperAndCtx(t, keeperParams)

		// Common setup
		consumerKeeper.SetProviderClientID(ctx, "clientID") // Set expected provider clientID

		// Specific mock setup
		tc.mockSetup(ctx, mocks)

		err := consumerKeeper.VerifyProviderChain(ctx, tc.connectionHops)

		if tc.expError {
			require.Error(t, err, "invalid case did not return error")
		} else {
			require.NoError(t, err, "valid case returned error")
		}
		ctrl.Finish()
	}
}

// TestGetAllHeightToValsetUpdateIDs tests GetAllHeightToValsetUpdateIDs behaviour correctness
func TestGetAllHeightToValsetUpdateIDs(t *testing.T) {
	ck, ctx, ctrl, _ := testkeeper.GetConsumerKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	cases := []types.HeightToValsetUpdateID{
		{
			ValsetUpdateId: 2,
			Height:         22,
		},
		{
			ValsetUpdateId: 1,
			Height:         11,
		},
		{
			// normal execution should not have two HeightToValsetUpdateID
			// with the same ValsetUpdateId, but let's test it anyway
			ValsetUpdateId: 1,
			Height:         44,
		},
		{
			ValsetUpdateId: 3,
			Height:         33,
		},
	}
	expectedGetAllOrder := cases
	// sorting by Height
	sort.Slice(expectedGetAllOrder, func(i, j int) bool {
		return expectedGetAllOrder[i].Height < expectedGetAllOrder[j].Height
	})

	for _, c := range cases {
		ck.SetHeightValsetUpdateID(ctx, c.Height, c.ValsetUpdateId)
	}

	// iterate and check all results are returned
	result := ck.GetAllHeightToValsetUpdateIDs(ctx)
	require.Len(t, result, len(cases))
	require.Equal(t, expectedGetAllOrder, result)
}

// TestGetAllOutstandingDowntimes tests GetAllOutstandingDowntimes behaviour correctness
func TestGetAllOutstandingDowntimes(t *testing.T) {
	ck, ctx, ctrl, _ := testkeeper.GetConsumerKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	addresses := []sdk.ConsAddress{
		sdk.ConsAddress([]byte("consAddress2")),
		sdk.ConsAddress([]byte("consAddress1")),
		sdk.ConsAddress([]byte("consAddress4")),
		sdk.ConsAddress([]byte("consAddress3")),
	}
	expectedGetAllOrder := []types.OutstandingDowntime{}
	for _, addr := range addresses {
		expectedGetAllOrder = append(expectedGetAllOrder, types.OutstandingDowntime{ValidatorConsensusAddress: addr.String()})
	}
	// sorting by ConsAddress
	sort.Slice(expectedGetAllOrder, func(i, j int) bool {
		return bytes.Compare(addresses[i], addresses[j]) == -1
	})

	for _, addr := range addresses {
		ck.SetOutstandingDowntime(ctx, addr)
	}

	// iterate and check all results are returned in the expected order
	result := ck.GetAllOutstandingDowntimes(ctx)
	require.Len(t, result, len(addresses))
	require.Equal(t, result, expectedGetAllOrder)
}

func TestPrevStandaloneChainFlag(t *testing.T) {
	ck, ctx, ctrl, _ := testkeeper.GetConsumerKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// Test that the default value is false
	require.False(t, ck.IsPrevStandaloneChain(ctx))

	// Test that the value can be set and retrieved
	ck.MarkAsPrevStandaloneChain(ctx)
	require.True(t, ck.IsPrevStandaloneChain(ctx))
}

func TestDeleteHeadOfPendingPackets(t *testing.T) {
	consumerKeeper, ctx, ctrl, _ := testkeeper.GetConsumerKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// append some pending packets
	consumerKeeper.AppendPendingPacket(ctx, ccv.VscMaturedPacket, &ccv.ConsumerPacketData_VscMaturedPacketData{})
	consumerKeeper.AppendPendingPacket(ctx, ccv.SlashPacket, &ccv.ConsumerPacketData_SlashPacketData{})
	consumerKeeper.AppendPendingPacket(ctx, ccv.VscMaturedPacket, &ccv.ConsumerPacketData_VscMaturedPacketData{})

	// Check there's 3 pending packets, vsc matured at head
	pp := consumerKeeper.GetPendingPackets(ctx)
	require.Len(t, pp, 3)
	require.Equal(t, pp[0].Type, ccv.VscMaturedPacket)

	// Delete the head, confirm slash packet is now at head
	consumerKeeper.DeleteHeadOfPendingPackets(ctx)
	pp = consumerKeeper.GetPendingPackets(ctx)
	require.Len(t, pp, 2)
	require.Equal(t, pp[0].Type, ccv.SlashPacket)

	// Delete the head, confirm vsc matured packet is now at head
	consumerKeeper.DeleteHeadOfPendingPackets(ctx)
	pp = consumerKeeper.GetPendingPackets(ctx)
	require.Len(t, pp, 1)
	require.Equal(t, pp[0].Type, ccv.VscMaturedPacket)
}
