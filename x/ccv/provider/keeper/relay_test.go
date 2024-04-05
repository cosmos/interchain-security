package keeper_test

import (
	"strings"
	"testing"

	clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v7/modules/core/04-channel/types"
	ibctesting "github.com/cosmos/ibc-go/v7/testing"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"

	"cosmossdk.io/math"

	codectypes "github.com/cosmos/cosmos-sdk/codec/types"
	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	cryptotypes "github.com/cosmos/cosmos-sdk/crypto/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	abci "github.com/cometbft/cometbft/abci/types"

	"github.com/cosmos/interchain-security/v4/testutil/crypto"
	cryptotestutil "github.com/cosmos/interchain-security/v4/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/v4/testutil/keeper"
	"github.com/cosmos/interchain-security/v4/x/ccv/provider/keeper"
	"github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
	providertypes "github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/v4/x/ccv/types"
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
		mocks.MockStakingKeeper.EXPECT().GetLastValidators(ctx).Times(1)

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
//
// Note: Handling logic itself is not tested here.
func TestOnRecvVSCMaturedPacket(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()
	providerKeeper.SetParams(ctx, providertypes.DefaultParams())

	// Set channel to chain (faking multiple established channels)
	providerKeeper.SetChannelToChain(ctx, "channel-1", "chain-1")
	providerKeeper.SetChannelToChain(ctx, "channel-2", "chain-2")

	// Execute on recv for chain-1, confirm v1 result ack is returned
	err := executeOnRecvVSCMaturedPacket(t, &providerKeeper, ctx, "channel-1", 1)
	require.NoError(t, err)

	// Now queue a slash packet data instance for chain-2, confirm v1 result ack is returned
	err = executeOnRecvVSCMaturedPacket(t, &providerKeeper, ctx, "channel-2", 2)
	require.NoError(t, err)
}

// TestOnRecvDowntimeSlashPacket tests the OnRecvSlashPacket method specifically for downtime slash packets.
func TestOnRecvDowntimeSlashPacket(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()
	providerKeeper.SetParams(ctx, providertypes.DefaultParams())

	// Set channel to chain (faking multiple established channels)
	providerKeeper.SetChannelToChain(ctx, "channel-1", "chain-1")
	providerKeeper.SetChannelToChain(ctx, "channel-2", "chain-2")

	// Generate a new slash packet data instance with double sign infraction type
	packetData := testkeeper.GetNewSlashPacketData()
	packetData.Infraction = stakingtypes.Infraction_INFRACTION_DOWNTIME

	// Set a block height for the valset update id in the generated packet data
	providerKeeper.SetValsetUpdateBlockHeight(ctx, packetData.ValsetUpdateId, uint64(15))

	// Set slash meter to negative value and assert a bounce ack is returned
	providerKeeper.SetSlashMeter(ctx, math.NewInt(-5))
	ackResult, err := executeOnRecvSlashPacket(t, &providerKeeper, ctx, "channel-1", 1, packetData)
	require.Equal(t, ccv.SlashPacketBouncedResult, ackResult)
	require.NoError(t, err)

	// Also bounced for chain-2
	ackResult, err = executeOnRecvSlashPacket(t, &providerKeeper, ctx, "channel-2", 2, packetData)
	require.Equal(t, ccv.SlashPacketBouncedResult, ackResult)
	require.NoError(t, err)

	// Now set slash meter to positive value and assert slash packet handled result is returned
	providerKeeper.SetSlashMeter(ctx, math.NewInt(5))

	// Set the consumer validator
	providerKeeper.SetConsumerValidator(ctx, "chain-1", types.ConsumerValidator{ProviderConsAddr: packetData.Validator.Address})

	// Mock call to GetEffectiveValPower, so that it returns 2.
	providerAddr := providertypes.NewProviderConsAddress(packetData.Validator.Address)
	calls := []*gomock.Call{
		mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx, providerAddr.ToSdkConsAddr()).
			Return(stakingtypes.Validator{}, true).Times(1),
		mocks.MockStakingKeeper.EXPECT().GetLastValidatorPower(ctx, gomock.Any()).
			Return(int64(2)).Times(1),
	}

	// Add mocks for slash packet handling
	calls = append(calls,
		testkeeper.GetMocksForHandleSlashPacket(
			ctx, mocks, providerAddr, stakingtypes.Validator{Jailed: false}, true)...,
	)
	gomock.InOrder(calls...)

	// Execute on recv and confirm slash packet handled result is returned
	ackResult, err = executeOnRecvSlashPacket(t, &providerKeeper, ctx, "channel-1", 1, packetData)
	require.Equal(t, ccv.SlashPacketHandledResult, ackResult)
	require.NoError(t, err)

	// Require slash meter was decremented appropriately, 5-2=3
	require.Equal(t, int64(3), providerKeeper.GetSlashMeter(ctx).Int64())
}

// TestOnRecvDoubleSignSlashPacket tests the OnRecvSlashPacket method specifically for double-sign slash packets.
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

	require.True(t, providerKeeper.GetSlashLog(ctx,
		providertypes.NewProviderConsAddress(packetData.Validator.Address)))

	// slash log should be empty for a random validator address in this testcase
	randomAddress := cryptotestutil.NewCryptoIdentityFromIntSeed(100).ProviderConsAddress()
	require.False(t, providerKeeper.GetSlashLog(ctx, randomAddress))
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
	// this "dummy" consensus address won't be stored on the provider states
	dummyConsAddr := cryptotestutil.NewCryptoIdentityFromIntSeed(784987639).ConsumerConsAddress()

	testCases := []struct {
		name       string
		packetData ccv.SlashPacketData
		// The mocks that we expect to be called for the specified packet data.
		expectedCalls        func(sdk.Context, testkeeper.MockedKeepers, ccv.SlashPacketData) []*gomock.Call
		expectedSlashAcksLen int
	}{
		{
			"validator isn't a consumer validator",
			ccv.SlashPacketData{
				Validator:      abci.Validator{Address: dummyConsAddr.ToSdkConsAddr()},
				ValsetUpdateId: validVscID,
				Infraction:     stakingtypes.Infraction_INFRACTION_DOWNTIME,
			},
			func(ctx sdk.Context, mocks testkeeper.MockedKeepers,
				expectedPacketData ccv.SlashPacketData,
			) []*gomock.Call {
				return []*gomock.Call{}
			},
			0,
		},
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
		t.Run(tc.name, func(t *testing.T) {
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
			providerKeeper.SetConsumerValidator(ctx, chainId, types.ConsumerValidator{ProviderConsAddr: providerConsAddr.Address.Bytes()})

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
		})
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
	gomock.InOrder(
		mocks.MockStakingKeeper.EXPECT().GetUnbondingType(ctx, unbondingOpId).Return(stakingtypes.UnbondingType_Undefined, false),
	)

	err := pk.Hooks().AfterUnbondingInitiated(ctx, unbondingOpId)
	require.NoError(t, err)
	// Check that no unbonding op was stored
	_, found := pk.GetUnbondingOp(ctx, unbondingOpId)
	require.False(t, found)

	// Increment vscID
	pk.IncrementValidatorSetUpdateId(ctx)
	require.Equal(t, uint64(2), pk.GetValidatorSetUpdateId(ctx))

	// Register first consumer
	pk.SetConsumerClientId(ctx, "chain-1", "client-1")

	// Create 2 validators
	vals := []stakingtypes.Validator{}
	valsPk := []cryptotypes.PubKey{}
	for i := 0; i < 2; i++ {
		pubkey, err := cryptocodec.FromTmPubKeyInterface(cryptotestutil.NewCryptoIdentityFromIntSeed(54321 + i).TMCryptoPubKey())
		require.NoError(t, err)
		valsPk = append(valsPk, pubkey)
		pkAny, err := codectypes.NewAnyWithValue(pubkey)
		require.NoError(t, err)
		vals = append(vals, stakingtypes.Validator{ConsensusPubkey: pkAny})
	}

	// Opt-in one validator to consumer
	pk.SetConsumerValidator(ctx, "chain-1", types.ConsumerValidator{ProviderConsAddr: valsPk[0].Address()})

	// Start second unbonding
	unbondingOpId = 2
	gomock.InOrder(
		mocks.MockStakingKeeper.EXPECT().GetUnbondingType(ctx, unbondingOpId).Return(stakingtypes.UnbondingType_UnbondingDelegation, true),
		mocks.MockStakingKeeper.EXPECT().GetUnbondingDelegationByUnbondingID(ctx, unbondingOpId).Return(
			stakingtypes.UnbondingDelegation{
				ValidatorAddress: sdk.ValAddress([]byte{1}).String(),
			}, true),
		mocks.MockStakingKeeper.EXPECT().GetValidator(ctx, sdk.ValAddress([]byte{1})).
			Return(vals[0], true),
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

	// Opt-in both validators to second consumer
	pk.SetConsumerValidator(ctx, "chain-2", types.ConsumerValidator{ProviderConsAddr: valsPk[0].Address()})
	pk.SetConsumerValidator(ctx, "chain-2", types.ConsumerValidator{ProviderConsAddr: valsPk[1].Address()})

	// Start third and fourth unbonding
	unbondingOpIds := []uint64{3, 4}
	for _, id := range unbondingOpIds {
		gomock.InOrder(
			mocks.MockStakingKeeper.EXPECT().GetUnbondingType(ctx, id).Return(stakingtypes.UnbondingType_Redelegation, true),
			mocks.MockStakingKeeper.EXPECT().GetRedelegationByUnbondingID(ctx, id).Return(
				stakingtypes.Redelegation{
					ValidatorSrcAddress: sdk.ValAddress([]byte{1}).String(),
				}, true),
			mocks.MockStakingKeeper.EXPECT().GetValidator(ctx, sdk.ValAddress([]byte{1})).
				Return(vals[0], true),
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

	// Increment vscID
	pk.IncrementValidatorSetUpdateId(ctx)
	require.Equal(t, uint64(4), pk.GetValidatorSetUpdateId(ctx))

	// Start fith unbonding
	unbondingOpId = 5
	gomock.InOrder(
		mocks.MockStakingKeeper.EXPECT().GetUnbondingType(ctx, unbondingOpId).Return(stakingtypes.UnbondingType_ValidatorUnbonding, true),
		mocks.MockStakingKeeper.EXPECT().GetValidatorByUnbondingID(ctx, unbondingOpId).Return(
			stakingtypes.Validator{
				OperatorAddress: sdk.ValAddress([]byte{1}).String(),
			}, true),
		mocks.MockStakingKeeper.EXPECT().GetValidator(ctx, sdk.ValAddress([]byte{1})).
			Return(vals[1], true),
		mocks.MockStakingKeeper.EXPECT().PutUnbondingOnHold(ctx, unbondingOpId).Return(nil),
	)
	err = pk.Hooks().AfterUnbondingInitiated(ctx, unbondingOpId)
	require.NoError(t, err)

	// Check that an unbonding op was stored for chain-2 only
	// since it's the only consumer the unbonding validator has opted-in to
	expectedChains = []string{"chain-2"}
	unbondingOp, found = pk.GetUnbondingOp(ctx, unbondingOpId)
	require.True(t, found)
	require.Equal(t, unbondingOpId, unbondingOp.Id)
	require.Equal(t, expectedChains, unbondingOp.UnbondingConsumerChains)

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

// TestEndBlockVSU tests that during `EndBlockVSU`, we only queue VSC packets at the boundaries of an epoch
func TestEndBlockVSU(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	chainID := "chainID"

	providerKeeper.SetTopN(ctx, chainID, 100)

	// 10 blocks constitute an epoch
	params := providertypes.DefaultParams()
	params.BlocksPerEpoch = 10
	providerKeeper.SetParams(ctx, params)

	// create 4 sample lastValidators
	var lastValidators []stakingtypes.Validator
	var valAddresses []sdk.ValAddress
	for i := 0; i < 4; i++ {
		validator := crypto.NewCryptoIdentityFromIntSeed(i).SDKStakingValidator()
		lastValidators = append(lastValidators, validator)
		valAddresses = append(valAddresses, validator.GetOperator())
		mocks.MockStakingKeeper.EXPECT().GetLastValidatorPower(gomock.Any(), validator.GetOperator()).Return(int64(i + 1)).AnyTimes()
	}

	mocks.MockStakingKeeper.EXPECT().GetLastValidators(gomock.Any()).Return(lastValidators).AnyTimes()

	// set a sample client for a consumer chain so that `GetAllConsumerChains` in `QueueVSCPackets` iterates at least once
	providerKeeper.SetConsumerClientId(ctx, chainID, "clientID")

	// with block height of 1 we do not expect any queueing of VSC packets
	ctx = ctx.WithBlockHeight(1)
	providerKeeper.EndBlockVSU(ctx)
	require.Equal(t, 0, len(providerKeeper.GetPendingVSCPackets(ctx, chainID)))

	// with block height of 5 we do not expect any queueing of VSC packets
	ctx = ctx.WithBlockHeight(5)
	providerKeeper.EndBlockVSU(ctx)
	require.Equal(t, 0, len(providerKeeper.GetPendingVSCPackets(ctx, chainID)))

	// with block height of 10 we expect the queueing of one VSC packet
	ctx = ctx.WithBlockHeight(10)
	providerKeeper.EndBlockVSU(ctx)
	require.Equal(t, 1, len(providerKeeper.GetPendingVSCPackets(ctx, chainID)))

	// With block height of 15 we expect no additional queueing of a VSC packet.
	// Note that the pending VSC packet is still there because `SendVSCPackets` does not send the packet. We
	// need to mock channels, etc. for this to work, and it's out of scope for this test.
	ctx = ctx.WithBlockHeight(15)
	providerKeeper.EndBlockVSU(ctx)
	require.Equal(t, 1, len(providerKeeper.GetPendingVSCPackets(ctx, chainID)))
}
