package keeper_test

import (
	"testing"

	"github.com/golang/mock/gomock"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
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
