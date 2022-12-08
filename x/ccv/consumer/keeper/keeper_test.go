package keeper_test

import (
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

// TestVSCPacketQueue tests getter, setter, and iterator functionality for the VSC packet queue
func TestVSCPacketQueue(t *testing.T) {
	consumerKeeper, ctx, ctrl, _ := testkeeper.GetConsumerKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	maturingVSCPacket := consumerKeeper.GetAllVSCPacketMaturityTimes(ctx)
	require.Len(t, maturingVSCPacket, 0)

	now := ctx.BlockHeader().Time
	vscPackets := []types.MaturingVSCPacket{
		{
			VscId:        1,
			MaturityTime: now,
		},
		{
			VscId:        2,
			MaturityTime: now,
		},
		{
			VscId:        3,
			MaturityTime: now.Add(time.Hour),
		},
		{
			VscId:        4,
			MaturityTime: now.Add(2 * time.Hour),
		},
	}

	for _, vscPacket := range vscPackets {
		consumerKeeper.InsertVSCPacketQueue(ctx, vscPacket.VscId, vscPacket.MaturityTime)
	}

	maturingVSCPacket = consumerKeeper.GetAllVSCPacketMaturityTimes(ctx)
	require.Equal(t, vscPackets, maturingVSCPacket)

	vscIDs := consumerKeeper.GetVSCPacketQueueTimeSlice(ctx, vscPackets[0].MaturityTime)
	require.Len(t, vscIDs, 2)
	require.Equal(t, vscPackets[0].VscId, vscIDs[0])
	require.Equal(t, vscPackets[1].VscId, vscIDs[1])

	vscIDs = consumerKeeper.DequeueAllMatureVSCPacketQueue(ctx)
	require.Len(t, vscIDs, 2)
	require.Equal(t, vscPackets[0].VscId, vscIDs[0])
	require.Equal(t, vscPackets[1].VscId, vscIDs[1])

	maturingVSCPacket = consumerKeeper.GetAllVSCPacketMaturityTimes(ctx)
	require.Len(t, maturingVSCPacket, 2)
	require.Equal(t, vscPackets[2].VscId, maturingVSCPacket[0].VscId)
	require.Equal(t, vscPackets[3].VscId, maturingVSCPacket[1].VscId)

	newCtx := ctx.WithBlockTime(time.Now().Add(3 * time.Hour))
	vscIDs = consumerKeeper.DequeueAllMatureVSCPacketQueue(newCtx)
	require.Len(t, vscIDs, 2)
	require.Equal(t, vscPackets[2].VscId, vscIDs[0])
	require.Equal(t, vscPackets[3].VscId, vscIDs[1])

	maturingVSCPacket = consumerKeeper.GetAllVSCPacketMaturityTimes(newCtx)
	require.Len(t, maturingVSCPacket, 0)
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

func TestSetPendingPackets(t *testing.T) {

	consumerKeeper, ctx, ctrl, _ := testkeeper.GetConsumerKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// prepare test setup
	dataPackets := []types.ConsumerPacket{
		{
			Type: types.VscMaturedPacket,
			Data: ccv.NewVSCMaturedPacketData(1).GetBytes(),
		},
		{
			Type: types.VscMaturedPacket,
			Data: ccv.NewVSCMaturedPacketData(2).GetBytes(),
		},
		{
			Type: types.SlashPacket,
			Data: ccv.NewSlashPacketData(
				abci.Validator{Address: ed25519.GenPrivKey().PubKey().Address(), Power: int64(0)},
				3,
				stakingtypes.DoubleSign,
			).GetBytes(),
		},
		{
			Type: types.VscMaturedPacket,
			Data: ccv.NewVSCMaturedPacketData(3).GetBytes(),
		},
	}
	consumerKeeper.SetPendingPackets(ctx, types.ConsumerPackets{List: dataPackets})

	storedDataPackets := consumerKeeper.GetPendingPackets(ctx)
	require.NotEmpty(t, storedDataPackets)
	require.Equal(t, dataPackets, storedDataPackets.List)

	slashPacket := ccv.NewSlashPacketData(
		abci.Validator{Address: ed25519.GenPrivKey().PubKey().Address(),
			Power: int64(2)},
		uint64(4),
		stakingtypes.Downtime,
	)
	dataPackets = append(dataPackets, types.ConsumerPacket{Type: types.SlashPacket, Data: slashPacket.GetBytes()})
	consumerKeeper.AppendPendingPacket(ctx, dataPackets[len(dataPackets)-1])
	storedDataPackets = consumerKeeper.GetPendingPackets(ctx)
	require.NotEmpty(t, storedDataPackets)
	require.Equal(t, dataPackets, storedDataPackets.List)

	vscMaturedPakcet := ccv.NewVSCMaturedPacketData(4)
	dataPackets = append(dataPackets, types.ConsumerPacket{Type: types.VscMaturedPacket, Data: vscMaturedPakcet.GetBytes()})
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
