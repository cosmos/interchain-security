package keeper_test

import (
	"testing"

	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	sdk "github.com/cosmos/cosmos-sdk/types"
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

	consumerKeeper, ctx, ctrl, _ := testkeeper.GetConsumerKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerKeeper.SetPacketMaturityTime(ctx, 1, 10)
	consumerKeeper.SetPacketMaturityTime(ctx, 2, 25)
	consumerKeeper.SetPacketMaturityTime(ctx, 5, 15)
	consumerKeeper.SetPacketMaturityTime(ctx, 6, 40)

	consumerKeeper.DeletePacketMaturityTime(ctx, 6)

	require.Equal(t, uint64(10), consumerKeeper.GetPacketMaturityTime(ctx, 1))
	require.Equal(t, uint64(25), consumerKeeper.GetPacketMaturityTime(ctx, 2))
	require.Equal(t, uint64(15), consumerKeeper.GetPacketMaturityTime(ctx, 5))
	require.Equal(t, uint64(0), consumerKeeper.GetPacketMaturityTime(ctx, 3))
	require.Equal(t, uint64(0), consumerKeeper.GetPacketMaturityTime(ctx, 6))

	orderedTimes := [][]uint64{{1, 10}, {2, 25}, {5, 15}}
	i := 0

	consumerKeeper.IteratePacketMaturityTime(ctx, func(seq, time uint64) bool {
		// require that we iterate through unbonding time in order of sequence
		require.Equal(t, orderedTimes[i][0], seq)
		require.Equal(t, orderedTimes[i][1], time)
		i++
		return false
	})
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

// TestPendingSlashRequests tests the getter, setter, appending method, and deletion method for pending slash requests
func TestPendingSlashRequests(t *testing.T) {

	consumerKeeper, ctx, ctrl, _ := testkeeper.GetConsumerKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// prepare test setup by storing 10 pending slash requests
	requests := []types.SlashRequest{}
	for i := 0; i < 10; i++ {
		requests = append(requests, types.SlashRequest{})
		consumerKeeper.SetPendingSlashRequests(ctx, types.SlashRequests{Requests: requests})
	}

	// test set, append and clear operations
	testCases := []struct {
		operation func()
		expLen    int
	}{{
		operation: func() {},
		expLen:    10,
	}, {
		operation: func() { consumerKeeper.AppendPendingSlashRequests(ctx, types.SlashRequest{}) },
		expLen:    11,
	}, {
		operation: func() { consumerKeeper.DeletePendingSlashRequests(ctx) },
		expLen:    0,
	},
	}

	for _, tc := range testCases {
		tc.operation()
		requests := consumerKeeper.GetPendingSlashRequests(ctx)
		require.Len(t, requests.Requests, tc.expLen)
	}
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
