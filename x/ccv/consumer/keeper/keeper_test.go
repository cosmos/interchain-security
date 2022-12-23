package keeper_test

import (
	"bytes"
	"sort"
	"testing"
	"time"

	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	conntypes "github.com/cosmos/ibc-go/v3/modules/core/03-connection/types"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	"github.com/cosmos/interchain-security/x/ccv/consumer/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"
	abci "github.com/tendermint/tendermint/abci/types"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
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

	err = consumerKeeper.SetPendingChanges(ctx, pd)
	require.NoError(t, err)
	gotPd, ok := consumerKeeper.GetPendingChanges(ctx)
	require.True(t, ok)
	require.Equal(t, &pd, gotPd, "packet data in store does not equal packet data set")
	consumerKeeper.DeletePendingChanges(ctx)
	gotPd, ok = consumerKeeper.GetPendingChanges(ctx)
	require.False(t, ok)
	require.Nil(t, gotPd, "got non-nil pending changes after Delete")
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
	// Explicitly register codec with public key interface
	keeperParams.RegisterSdkCryptoCodecInterfaces()
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
	// Explicitly register codec with public key interface
	keeperParams.RegisterSdkCryptoCodecInterfaces()
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

func TestSetPendingPackets(t *testing.T) {

	consumerKeeper, ctx, ctrl, _ := testkeeper.GetConsumerKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// prepare test setup
	dataPackets := []ccv.ConsumerPacketData{
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
			Data: &ccv.ConsumerPacketData_SlashPacketData{SlashPacketData: ccv.NewSlashPacketData(
				abci.Validator{Address: ed25519.GenPrivKey().PubKey().Address(), Power: int64(0)},
				3,
				stakingtypes.DoubleSign,
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
	consumerKeeper.SetPendingPackets(ctx, ccv.ConsumerPacketDataList{List: dataPackets})

	storedDataPackets := consumerKeeper.GetPendingPackets(ctx)
	require.NotEmpty(t, storedDataPackets)
	require.Equal(t, dataPackets, storedDataPackets.List)

	slashPacket := ccv.NewSlashPacketData(
		abci.Validator{Address: ed25519.GenPrivKey().PubKey().Address(),
			Power: int64(2)},
		uint64(4),
		stakingtypes.Downtime,
	)
	dataPackets = append(dataPackets, ccv.ConsumerPacketData{
		Type: ccv.SlashPacket,
		Data: &ccv.ConsumerPacketData_SlashPacketData{SlashPacketData: slashPacket}},
	)
	consumerKeeper.AppendPendingPacket(ctx, dataPackets[len(dataPackets)-1])
	storedDataPackets = consumerKeeper.GetPendingPackets(ctx)
	require.NotEmpty(t, storedDataPackets)
	require.Equal(t, dataPackets, storedDataPackets.List)

	vscMaturedPakcet := ccv.NewVSCMaturedPacketData(4)
	dataPackets = append(dataPackets, ccv.ConsumerPacketData{Type: ccv.VscMaturedPacket,
		Data: &ccv.ConsumerPacketData_VscMaturedPacketData{VscMaturedPacketData: vscMaturedPakcet}},
	)
	consumerKeeper.AppendPendingPacket(ctx, dataPackets[len(dataPackets)-1])
	storedDataPackets = consumerKeeper.GetPendingPackets(ctx)
	require.NotEmpty(t, storedDataPackets)
	require.Equal(t, dataPackets, storedDataPackets.List)

	consumerKeeper.DeletePendingDataPackets(ctx)
	storedDataPackets = consumerKeeper.GetPendingPackets(ctx)
	require.Empty(t, storedDataPackets)
	require.Len(t, storedDataPackets.List, 0)
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
