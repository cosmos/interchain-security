package keeper_test

import (
	"sort"
	"strings"
	"testing"
	"time"

	"cosmossdk.io/math"
	capabilitytypes "github.com/cosmos/ibc-go/modules/capability/types"
	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v8/modules/core/04-channel/types"
	ibctesting "github.com/cosmos/ibc-go/v8/testing"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	abci "github.com/cometbft/cometbft/abci/types"

	cryptotestutil "github.com/cosmos/interchain-security/v5/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/v5/testutil/keeper"
	"github.com/cosmos/interchain-security/v5/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/v5/x/ccv/types"
)

// TestQueueVSCPackets tests queueing validator set updates.
func TestQueueVSCPackets(t *testing.T) {
	_, _, key := ibctesting.GenerateKeys(t, 1)
	tmPubKey, _ := cryptocodec.ToCmtProtoPublicKey(key)

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
		testkeeper.SetupMocksForLastBondedValidatorsExpectation(mocks.MockStakingKeeper, 0, []stakingtypes.Validator{}, 1)

		mocks.MockStakingKeeper.EXPECT().GetBondedValidatorsByPower(gomock.Any()).Return([]stakingtypes.Validator{}, nil).AnyTimes()

		pk := testkeeper.NewInMemProviderKeeper(keeperParams, mocks)
		// no-op if tc.packets is empty
		pk.AppendPendingVSCPackets(ctx, chainID, tc.packets...)

		err := pk.QueueVSCPackets(ctx)
		require.NoError(t, err)
		pending := pk.GetPendingVSCPackets(ctx, chainID)
		require.Len(t, pending, tc.expectedQueueSize, "pending vsc queue mismatch (%v != %v) in case: '%s'", tc.expectedQueueSize, len(pending), tc.name)

		// next valset update ID -> default value in tests is 0
		// each call to QueueValidatorUpdates will increment the ValidatorUpdateID
		valUpdateID := pk.GetValidatorSetUpdateId(ctx)
		require.Equal(t, tc.expectNextValsetUpdateId, valUpdateID, "valUpdateID (%v != %v) mismatch in case: '%s'", tc.expectNextValsetUpdateId, valUpdateID, tc.name)
	}
}

// TestQueueVSCPacketsDoesNotResetConsumerValidatorsHeights checks that the heights of consumer validators are not
// getting incorrectly updated
func TestQueueVSCPacketsDoesNotResetConsumerValidatorsHeights(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	chainHeight := int64(987654321)
	ctx = ctx.WithBlockHeight(chainHeight)
	providerKeeper.SetParams(ctx, providertypes.DefaultParams())

	// mock 2 bonded validators
	valA := createStakingValidator(ctx, mocks, 1, 1)
	valAConsAddr, _ := valA.GetConsAddr()
	valAPubKey, _ := valA.TmConsPublicKey()
	mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx, valAConsAddr).Return(valA, nil).AnyTimes()
	valB := createStakingValidator(ctx, mocks, 2, 2)
	valBConsAddr, _ := valB.GetConsAddr()
	mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx, valBConsAddr).Return(valB, nil).AnyTimes()
	testkeeper.SetupMocksForLastBondedValidatorsExpectation(mocks.MockStakingKeeper, 2, []stakingtypes.Validator{valA, valB}, -1)

	// set a consumer client id and its phase, so we have a consumer chain (i.e., `GetAllConsumerWithIBCClients` is non-empty)
	providerKeeper.SetConsumerClientId(ctx, "consumerId", "clientID")
	providerKeeper.SetConsumerPhase(ctx, "consumerId", providertypes.ConsumerPhase_CONSUMER_PHASE_LAUNCHED)

	// opt in validator A and set as a consumer validator
	providerKeeper.SetOptedIn(ctx, "consumerId", providertypes.NewProviderConsAddress(valAConsAddr))
	consumerValidatorA := providertypes.ConsensusValidator{
		ProviderConsAddr: valAConsAddr,
		Power:            1,
		PublicKey:        &valAPubKey,
		JoinHeight:       123456789,
	}
	providerKeeper.SetConsumerValidator(ctx, "consumerId", consumerValidatorA)

	// Opt in validator B. Note that validator B is not a consumer validator and hence would become a consumer
	// validator for the first time after the `QueueVSCPackets` call.
	providerKeeper.SetOptedIn(ctx, "consumerId", providertypes.NewProviderConsAddress(valBConsAddr))

	// set power shaping params
	err := providerKeeper.SetConsumerPowerShapingParameters(ctx, "consumerId", providertypes.PowerShapingParameters{})
	require.NoError(t, err)

	err = providerKeeper.QueueVSCPackets(ctx)
	require.NoError(t, err)

	// the height of consumer validator A should not be modified because A was already a consumer validator
	cv, _ := providerKeeper.GetConsumerValidator(ctx, "consumerId", providertypes.NewProviderConsAddress(valAConsAddr))
	require.Equal(t, consumerValidatorA.JoinHeight, cv.JoinHeight, "the consumer validator's height was erroneously modified")

	// the height of consumer validator B is set to be the same as the one of the current chain height because this
	// consumer validator becomes a consumer validator for the first time (i.e., was not a consumer validator in the previous epoch)
	cv, _ = providerKeeper.GetConsumerValidator(ctx, "consumerId", providertypes.NewProviderConsAddress(valBConsAddr))
	require.Equal(t, chainHeight, cv.JoinHeight, "the consumer validator's height was not correctly set")
}

// TestOnRecvDowntimeSlashPacket tests the OnRecvSlashPacket method specifically for downtime slash packets.
func TestOnRecvDowntimeSlashPacket(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()
	providerKeeper.SetParams(ctx, providertypes.DefaultParams())

	// Set channel to chain (faking multiple established channels)
	providerKeeper.SetChannelToConsumerId(ctx, "channel-1", "chain-1")
	providerKeeper.SetChannelToConsumerId(ctx, "channel-2", "chain-2")

	// Generate a new slash packet data instance with double sign infraction type
	packetData := testkeeper.GetNewSlashPacketData()
	packetData.Infraction = stakingtypes.Infraction_INFRACTION_DOWNTIME

	// Set a block height for the valset update id in the generated packet data
	providerKeeper.SetValsetUpdateBlockHeight(ctx, packetData.ValsetUpdateId, uint64(15))

	// Set consumer validator
	providerKeeper.SetConsumerValidator(ctx, "chain-1", providertypes.ConsensusValidator{
		ProviderConsAddr: packetData.Validator.Address,
	})

	// Set slash meter to negative value and assert a bounce ack is returned
	providerKeeper.SetSlashMeter(ctx, math.NewInt(-5))
	ackResult, err := executeOnRecvSlashPacket(t, &providerKeeper, ctx, "channel-1", 1, packetData)
	require.Equal(t, ccv.SlashPacketBouncedResult, ackResult)
	require.NoError(t, err)

	// Set consumer validator
	providerKeeper.SetConsumerValidator(ctx, "chain-2", providertypes.ConsensusValidator{
		ProviderConsAddr: packetData.Validator.Address,
	})

	// Also bounced for chain-2
	ackResult, err = executeOnRecvSlashPacket(t, &providerKeeper, ctx, "channel-2", 2, packetData)
	require.Equal(t, ccv.SlashPacketBouncedResult, ackResult)
	require.NoError(t, err)

	// Now set slash meter to positive value and assert slash packet handled result is returned
	providerKeeper.SetSlashMeter(ctx, math.NewInt(5))

	// Set the consumer validator
	providerKeeper.SetConsumerValidator(ctx, "chain-1", providertypes.ConsensusValidator{ProviderConsAddr: packetData.Validator.Address})

	// Mock call to GetEffectiveValPower, so that it returns 2.
	providerAddr := providertypes.NewProviderConsAddress(packetData.Validator.Address)
	calls := []*gomock.Call{
		mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx, providerAddr.ToSdkConsAddr()).
			Return(stakingtypes.Validator{
				// provided address must be valid so it can be processed correctly
				// by k.ValidatorAddressCodec().StringToBytes(val.GetOperator()) call in GetEffectiveValPower()
				OperatorAddress: sdk.ValAddress(packetData.Validator.Address).String(),
			}, nil).Times(1),
		mocks.MockStakingKeeper.EXPECT().GetLastValidatorPower(ctx, gomock.Any()).
			Return(int64(2), nil).Times(1),
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
	providerKeeper.SetChannelToConsumerId(ctx, "channel-1", "chain-1")
	providerKeeper.SetChannelToConsumerId(ctx, "channel-2", "chain-2")

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
		providerKeeper.SetChannelToConsumerId(ctx, "channel-9", "consumer-chain-id")

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

	testCases := []struct {
		name       string
		packetData ccv.SlashPacketData
		// The mocks that we expect to be called for the specified packet data.
		expectedCalls                       func(sdk.Context, testkeeper.MockedKeepers, ccv.SlashPacketData) []*gomock.Call
		expectedSlashAcksLen                int
		expectedSlashAckConsumerConsAddress providertypes.ConsumerConsAddress
	}{
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
						stakingtypes.Validator{}, stakingtypes.ErrNoValidatorFound, // false = Not found.
					).Times(1),
				}
			},
			0,
			consumerConsAddr,
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
						stakingtypes.Validator{}, nil, // nil = no error.
					).Times(1),
					// Execution will stop after this call as validator is tombstoned.
					mocks.MockSlashingKeeper.EXPECT().IsTombstoned(ctx,
						providerConsAddr.ToSdkConsAddr()).Return(true).Times(1),
				}
			},
			0,
			consumerConsAddr,
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
						stakingtypes.Validator{}, nil,
					).Times(1),

					mocks.MockSlashingKeeper.EXPECT().IsTombstoned(ctx,
						providerConsAddr.ToSdkConsAddr()).Return(false).Times(1),
				}
			},
			0,
			consumerConsAddr,
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
			consumerConsAddr,
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
			consumerConsAddr,
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
			providerKeeper.SetConsumerValidator(ctx, chainId, providertypes.ConsensusValidator{ProviderConsAddr: providerConsAddr.Address.Bytes()})

			// Execute method and assert expected mock calls.
			providerKeeper.HandleSlashPacket(ctx, chainId, tc.packetData)

			require.Equal(t, tc.expectedSlashAcksLen, len(providerKeeper.GetSlashAcks(ctx, chainId)))

			if tc.expectedSlashAcksLen == 1 {
				// must match the consumer address
				require.Equal(t, tc.expectedSlashAckConsumerConsAddress.String(), providerKeeper.GetSlashAcks(ctx, chainId)[0])
				require.NotEqual(t, providerConsAddr.String(), providerKeeper.GetSlashAcks(ctx, chainId)[0])
				require.NotEqual(t, providerConsAddr.String(), consumerConsAddr.String())
			}

			ctrl.Finish()
		})
	}
}

// TestSendVSCPacketsToChainFailure tests the SendVSCPacketsToChain method failing
func TestSendVSCPacketsToChainFailure(t *testing.T) {
	// Keeper setup
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()
	providerKeeper.SetParams(ctx, providertypes.DefaultParams())

	// Append mocks for full consumer setup
	mockCalls := testkeeper.GetMocksForSetConsumerChain(ctx, &mocks, "consumerId")

	// Set 3 pending vsc packets
	providerKeeper.AppendPendingVSCPackets(ctx, "consumerId", []ccv.ValidatorSetChangePacketData{{}, {}, {}}...)

	// append mocks for the channel keeper to return an error
	mockCalls = append(mockCalls,
		mocks.MockChannelKeeper.EXPECT().GetChannel(ctx, ccv.ProviderPortID,
			"CCVChannelID").Return(channeltypes.Channel{}, false).Times(1),
	)

	// Append mocks for expected call to DeleteConsumerChain
	mockCalls = append(mockCalls, testkeeper.GetMocksForDeleteConsumerChain(ctx, &mocks)...)

	// Assert mock calls hit
	gomock.InOrder(mockCalls...)

	// Execute setup
	providerKeeper.SetConsumerClientId(ctx, "consumerId", "clientID")
	err := providerKeeper.SetConsumerChain(ctx, "channelID")
	require.NoError(t, err)

	unbondingTime := 123 * time.Second
	mocks.MockStakingKeeper.EXPECT().UnbondingTime(gomock.Any()).Return(unbondingTime, nil).AnyTimes()

	// No error should occur, DeleteConsumerChain should be called
	err = providerKeeper.SendVSCPacketsToChain(ctx, "consumerId", "CCVChannelID")
	require.NoError(t, err)

	// Verify the chain is about to be deleted
	removalTime, err := providerKeeper.GetConsumerRemovalTime(ctx, "consumerId")
	require.NoError(t, err)
	require.Equal(t, ctx.BlockTime().Add(unbondingTime), removalTime)

	// Increase the block time by `unbondingTime` so the chain actually gets deleted
	ctx = ctx.WithBlockTime(ctx.BlockTime().Add(unbondingTime))
	providerKeeper.BeginBlockRemoveConsumers(ctx)

	// Pending VSC packets should be deleted in DeleteConsumerChain
	require.Empty(t, providerKeeper.GetPendingVSCPackets(ctx, "consumerId"))
	require.Equal(t, providertypes.ConsumerPhase_CONSUMER_PHASE_DELETED, providerKeeper.GetConsumerPhase(ctx, "consumerId"))
}

// TestOnTimeoutPacketWithNoChainFound tests the `OnTimeoutPacket` method fails when no chain is found
func TestOnTimeoutPacketWithNoChainFound(t *testing.T) {
	// Keeper setup
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// We do not `SetChannelToConsumerId` for "channelID" and therefore `OnTimeoutPacket` fails
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

	testkeeper.SetupForDeleteConsumerChain(t, ctx, &providerKeeper, mocks, "consumerId")
	mocks.MockChannelKeeper.EXPECT().GetChannel(gomock.Any(), ccv.ProviderPortID, "channelID").Return(
		channeltypes.Channel{State: channeltypes.OPEN,
			ConnectionHops: []string{"connectionID"},
		}, true,
	).Times(1)
	dummyCap := &capabilitytypes.Capability{}
	mocks.MockScopedKeeper.EXPECT().GetCapability(gomock.Any(), gomock.Any()).Return(dummyCap, true).Times(1)
	mocks.MockChannelKeeper.EXPECT().ChanCloseInit(gomock.Any(), ccv.ProviderPortID, "channelID", dummyCap).Times(1)

	unbondingTime := 123 * time.Second
	mocks.MockStakingKeeper.EXPECT().UnbondingTime(gomock.Any()).Return(unbondingTime, nil).AnyTimes()

	packet := channeltypes.Packet{
		SourceChannel: "channelID",
	}
	err := providerKeeper.OnTimeoutPacket(ctx, packet)
	require.NoError(t, err)

	// increase the block time by `unbondingTime` so the chain actually gets deleted
	ctx = ctx.WithBlockTime(ctx.BlockTime().Add(unbondingTime))
	providerKeeper.BeginBlockRemoveConsumers(ctx)

	testkeeper.TestProviderStateIsCleanedAfterConsumerChainIsDeleted(t, ctx, providerKeeper, "consumerId", "channelID", false)
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
	testkeeper.SetupForDeleteConsumerChain(t, ctx, &providerKeeper, mocks, "consumerId")
	packet := channeltypes.Packet{
		SourceChannel: "channelID",
	}

	unbondingTime := 123 * time.Second
	mocks.MockStakingKeeper.EXPECT().UnbondingTime(gomock.Any()).Return(unbondingTime, nil).AnyTimes()
	mocks.MockChannelKeeper.EXPECT().GetChannel(gomock.Any(), ccv.ProviderPortID, "channelID").Return(
		channeltypes.Channel{State: channeltypes.OPEN,
			ConnectionHops: []string{"connectionID"},
		}, true,
	).Times(1)
	dummyCap := &capabilitytypes.Capability{}
	mocks.MockScopedKeeper.EXPECT().GetCapability(gomock.Any(), gomock.Any()).Return(dummyCap, true).Times(1)
	mocks.MockChannelKeeper.EXPECT().ChanCloseInit(gomock.Any(), ccv.ProviderPortID, "channelID", dummyCap).Times(1)

	err = providerKeeper.OnAcknowledgementPacket(ctx, packet, ackError)
	require.NoError(t, err)

	// increase the block time by `unbondingTime` so the chain actually gets deleted
	ctx = ctx.WithBlockTime(ctx.BlockTime().Add(unbondingTime))
	providerKeeper.BeginBlockRemoveConsumers(ctx)

	testkeeper.TestProviderStateIsCleanedAfterConsumerChainIsDeleted(t, ctx, providerKeeper, "consumerId", "channelID", false)
}

// TestEndBlockVSU tests that during `EndBlockVSU`, we only queue VSC packets at the boundaries of an epoch
func TestEndBlockVSU(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerId := "0"

	err := providerKeeper.SetConsumerPowerShapingParameters(ctx, "consumerId", providertypes.PowerShapingParameters{
		Top_N: 100,
	})
	require.NoError(t, err)

	// 10 blocks constitute an epoch
	params := providertypes.DefaultParams()
	params.BlocksPerEpoch = 10
	providerKeeper.SetParams(ctx, params)

	// create 4 sample lastValidators
	var lastValidators []stakingtypes.Validator
	for i := 0; i < 4; i++ {
		validator := cryptotestutil.NewCryptoIdentityFromIntSeed(i).SDKStakingValidator()
		lastValidators = append(lastValidators, validator)
		valAdrr, err := sdk.ValAddressFromBech32(validator.GetOperator())
		require.NoError(t, err)
		mocks.MockStakingKeeper.EXPECT().GetLastValidatorPower(gomock.Any(), valAdrr).Return(int64(i+1), nil).AnyTimes()
	}

	testkeeper.SetupMocksForLastBondedValidatorsExpectation(mocks.MockStakingKeeper, 5, lastValidators, -1)

	sort.Slice(lastValidators, func(i, j int) bool {
		return lastValidators[i].GetConsensusPower(sdk.DefaultPowerReduction) >
			lastValidators[j].GetConsensusPower(sdk.DefaultPowerReduction)
	})
	mocks.MockStakingKeeper.EXPECT().GetBondedValidatorsByPower(gomock.Any()).Return(lastValidators, nil).AnyTimes()

	// set a sample client for a launched consumer chain so that `GetAllConsumerWithIBCClients` in `QueueVSCPackets` iterates at least once
	providerKeeper.SetConsumerClientId(ctx, consumerId, "clientId")
	providerKeeper.SetConsumerPowerShapingParameters(ctx, consumerId, providertypes.PowerShapingParameters{Top_N: 100})
	providerKeeper.SetConsumerPhase(ctx, consumerId, providertypes.ConsumerPhase_CONSUMER_PHASE_LAUNCHED)

	// with block height of 1 we do not expect any queueing of VSC packets
	ctx = ctx.WithBlockHeight(1)
	_, err = providerKeeper.EndBlockVSU(ctx)
	require.NoError(t, err)
	require.Equal(t, 0, len(providerKeeper.GetPendingVSCPackets(ctx, consumerId)))

	// with block height of 5 we do not expect any queueing of VSC packets
	ctx = ctx.WithBlockHeight(5)
	_, err = providerKeeper.EndBlockVSU(ctx)
	require.NoError(t, err)
	require.Equal(t, 0, len(providerKeeper.GetPendingVSCPackets(ctx, consumerId)))

	// with block height of 10 we expect the queueing of one VSC packet
	ctx = ctx.WithBlockHeight(10)
	_, err = providerKeeper.EndBlockVSU(ctx)
	require.NoError(t, err)
	require.Equal(t, 1, len(providerKeeper.GetPendingVSCPackets(ctx, consumerId)))

	// With block height of 15 we expect no additional queueing of a VSC packet.
	// Note that the pending VSC packet is still there because `SendVSCPackets` does not send the packet. We
	// need to mock channels, etc. for this to work, and it's out of scope for this test.
	ctx = ctx.WithBlockHeight(15)
	_, err = providerKeeper.EndBlockVSU(ctx)
	require.NoError(t, err)
	require.Equal(t, 1, len(providerKeeper.GetPendingVSCPackets(ctx, consumerId)))
}

// TestProviderValidatorUpdates tests that the provider validator updates are correctly calculated,
// taking into account the MaxProviderConsensusValidators parameter
func TestProviderValidatorUpdates(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// Mocking bonded validators in the staking keeper.
	// be aware that the powers need to be in descending order
	validators := []stakingtypes.Validator{
		createStakingValidator(ctx, mocks, 30, 3),
		createStakingValidator(ctx, mocks, 20, 2),
		createStakingValidator(ctx, mocks, 10, 1),
	}
	mocks.MockStakingKeeper.EXPECT().GetBondedValidatorsByPower(ctx).Return(validators, nil).Times(1)

	// set up a validator that we will only use for the last provider consensus validator set
	removedValidator := createStakingValidator(ctx, mocks, 40, 4)

	// Set up the last provider consensus validators
	consensusVals := make([]providertypes.ConsensusValidator, 0, len(validators))
	// add the removed validator
	removedConsensusVal, err := providerKeeper.CreateProviderConsensusValidator(ctx, removedValidator)
	require.NoError(t, err)
	consensusVals = append(consensusVals, removedConsensusVal)
	for _, val := range validators[1:] { // skip the first validator (validator 3)
		consensusVal, err := providerKeeper.CreateProviderConsensusValidator(ctx, val)
		require.NoError(t, err)
		consensusVals = append(consensusVals, consensusVal)
	}
	// consensusVals is now [removedValidator, validator 2, validator 1]

	// Set the last provider consensus validator set
	providerKeeper.SetLastProviderConsensusValSet(ctx, consensusVals)

	// Set the max number of validators
	maxProviderConsensusValidators := int64(2)
	params := providerKeeper.GetParams(ctx)
	params.MaxProviderConsensusValidators = maxProviderConsensusValidators
	providerKeeper.SetParams(ctx, params)

	// expected validator updates

	// validator 3 is added
	// removed validator is set to 0 power
	// validator 1 is set to 0 power (because maxProviderConsensusValidators is 2)
	// validator 2 is untouched
	expectedUpdates := []abci.ValidatorUpdate{
		{
			PubKey: testkeeper.Must(validators[0].CmtConsPublicKey()),
			Power:  30,
		},
		{
			PubKey: testkeeper.Must(removedValidator.CmtConsPublicKey()),
			Power:  0,
		},
		{
			PubKey: testkeeper.Must(validators[2].CmtConsPublicKey()),
			Power:  0,
		},
	}

	// Execute the function
	updates, err := providerKeeper.ProviderValidatorUpdates(ctx)
	require.NoError(t, err)

	// Assertions
	require.ElementsMatch(t, expectedUpdates, updates, "The validator updates should match the expected updates")
}

// TestQueueVSCPacketsWithPowerCapping tests queueing validator set updates with power capping
func TestQueueVSCPacketsWithPowerCapping(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	providerKeeper.SetValidatorSetUpdateId(ctx, 1)

	valA := createStakingValidator(ctx, mocks, 1, 1) // 3.125% of the total voting power
	valAConsAddr, _ := valA.GetConsAddr()
	valAPubKey, _ := valA.TmConsPublicKey()
	mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx, valAConsAddr).Return(valA, nil).AnyTimes()
	valB := createStakingValidator(ctx, mocks, 3, 2) // 9.375% of the total voting power
	valBConsAddr, _ := valB.GetConsAddr()
	valBPubKey, _ := valB.TmConsPublicKey()
	mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx, valBConsAddr).Return(valB, nil).AnyTimes()
	valC := createStakingValidator(ctx, mocks, 4, 3) // 12.5% of the total voting power
	valCConsAddr, _ := valC.GetConsAddr()
	valCPubKey, _ := valC.TmConsPublicKey()
	mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx, valCConsAddr).Return(valC, nil).AnyTimes()
	valD := createStakingValidator(ctx, mocks, 8, 4) // 25% of the total voting power
	valDConsAddr, _ := valD.GetConsAddr()
	mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx, valDConsAddr).Return(valD, nil).AnyTimes()
	valE := createStakingValidator(ctx, mocks, 16, 5) // 50% of the total voting power
	valEConsAddr, _ := valE.GetConsAddr()
	valEPubKey, _ := valE.TmConsPublicKey()
	mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx, valEConsAddr).Return(valE, nil).AnyTimes()

	testkeeper.SetupMocksForLastBondedValidatorsExpectation(mocks.MockStakingKeeper, 5, []stakingtypes.Validator{valA, valB, valC, valD, valE}, -1)

	// add a consumer chain
	providerKeeper.SetConsumerClientId(ctx, "consumerId", "clientId")
	providerKeeper.SetConsumerPhase(ctx, "consumerId", providertypes.ConsumerPhase_CONSUMER_PHASE_LAUNCHED)

	err := providerKeeper.SetConsumerPowerShapingParameters(ctx, "consumerId", providertypes.PowerShapingParameters{
		Top_N:              50, // would opt in E
		ValidatorsPowerCap: 40, // set a power-capping of 40%
	})
	require.NoError(t, err)

	// opt in all validators
	providerKeeper.SetOptedIn(ctx, "consumerId", providertypes.NewProviderConsAddress(valAConsAddr))
	providerKeeper.SetOptedIn(ctx, "consumerId", providertypes.NewProviderConsAddress(valBConsAddr))
	providerKeeper.SetOptedIn(ctx, "consumerId", providertypes.NewProviderConsAddress(valCConsAddr))
	providerKeeper.SetOptedIn(ctx, "consumerId", providertypes.NewProviderConsAddress(valDConsAddr))

	// denylist validator D
	providerKeeper.SetDenylist(ctx, "consumerId", providertypes.NewProviderConsAddress(valDConsAddr))

	// set max provider consensus vals to include all validators
	params := providerKeeper.GetParams(ctx)
	params.MaxProviderConsensusValidators = 180
	providerKeeper.SetParams(ctx, params)

	err = providerKeeper.QueueVSCPackets(ctx)
	require.NoError(t, err)

	actualQueuedVSCPackets := providerKeeper.GetPendingVSCPackets(ctx, "consumerId")
	expectedQueuedVSCPackets := []ccv.ValidatorSetChangePacketData{
		ccv.NewValidatorSetChangePacketData(
			[]abci.ValidatorUpdate{
				// validator D is not here because it was denylisted
				// powers have changed because of power capping
				{
					PubKey: valEPubKey,
					Power:  9,
				},
				{
					PubKey: valCPubKey,
					Power:  6,
				},
				{
					PubKey: valBPubKey,
					Power:  5,
				},
				{
					PubKey: valAPubKey,
					Power:  4,
				},
			},
			1,
			nil),
	}

	require.Equal(t, expectedQueuedVSCPackets, actualQueuedVSCPackets)
}

// TestBlocksUntilNextEpoch tests the `BlocksUntilNextEpoch` method
func TestBlocksUntilNextEpoch(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// 10 blocks constitute an epoch
	params := providertypes.DefaultParams()
	params.BlocksPerEpoch = 10
	providerKeeper.SetParams(ctx, params)

	// with block height of 1 we expect 9 blocks until the next epoch
	ctx = ctx.WithBlockHeight(1)
	require.Equal(t, int64(9), providerKeeper.BlocksUntilNextEpoch(ctx))

	// with block height of 5 we expect 5 blocks until the next epoch
	ctx = ctx.WithBlockHeight(5)
	require.Equal(t, int64(5), providerKeeper.BlocksUntilNextEpoch(ctx))

	// with block height of 10 we expect 0 blocks until the next epoch, since
	// this epoch is the one where we send the VSC packet
	ctx = ctx.WithBlockHeight(10)
	require.Equal(t, int64(0), providerKeeper.BlocksUntilNextEpoch(ctx))

	// with block height of 11 we expect 9 blocks until the next epoch
	ctx = ctx.WithBlockHeight(11)
	require.Equal(t, int64(9), providerKeeper.BlocksUntilNextEpoch(ctx))

	// with block height of 15 we expect 5 blocks until the next epoch
	ctx = ctx.WithBlockHeight(15)
	require.Equal(t, int64(5), providerKeeper.BlocksUntilNextEpoch(ctx))

	// with block height of 19 we expect 1 block until the next epoch
	ctx = ctx.WithBlockHeight(19)
	require.Equal(t, int64(1), providerKeeper.BlocksUntilNextEpoch(ctx))
}
