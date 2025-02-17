package keeper_test

import (
	"testing"

	clienttypes "github.com/cosmos/ibc-go/v10/modules/core/02-client/types"
	conntypes "github.com/cosmos/ibc-go/v10/modules/core/03-connection/types"
	channeltypes "github.com/cosmos/ibc-go/v10/modules/core/04-channel/types"
	ibctmtypes "github.com/cosmos/ibc-go/v10/modules/light-clients/07-tendermint"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"

	"cosmossdk.io/math"

	sdk "github.com/cosmos/cosmos-sdk/types"

	tmtypes "github.com/cometbft/cometbft/types"

	testkeeper "github.com/cosmos/interchain-security/v7/testutil/keeper"
	providertypes "github.com/cosmos/interchain-security/v7/x/ccv/provider/types"
)

func TestComputeConsumerTotalVotingPower(t *testing.T) {
	keeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// `ComputeConsumerTotalVotingPower` used in this test retrieves the blocks per epoch, so we need to set this param
	params := providertypes.DefaultParams()
	params.BlocksPerEpoch = 1
	keeper.SetParams(ctx, params)

	// increase the block height so validators are eligible for consumer rewards (see `IsEligibleForConsumerRewards`)
	ctx = ctx.WithBlockHeight(params.NumberOfEpochsToStartReceivingRewards * params.BlocksPerEpoch)

	createVal := func(power int64) tmtypes.Validator {
		signer := tmtypes.NewMockPV()
		val := tmtypes.NewValidator(signer.PrivKey.PubKey(), power)
		return *val
	}

	chainID := CONSUMER_CHAIN_ID
	expTotalPower := int64(0)

	// verify that the total power returned is equal to zero
	// when the consumer doesn't exist or has no validators.
	require.Zero(t, keeper.ComputeConsumerTotalVotingPower(
		ctx,
		chainID,
	))

	// set 5 validators to the consumer chain
	for i := 0; i < 5; i++ {
		val := createVal(int64(i))
		err := keeper.SetConsumerValidator(
			ctx,
			chainID,
			providertypes.ConsensusValidator{
				ProviderConsAddr: val.Address,
				Power:            val.VotingPower,
			},
		)
		require.NoError(t, err)

		expTotalPower += val.VotingPower
	}

	// compute the total power of opted-in validators
	res := keeper.ComputeConsumerTotalVotingPower(
		ctx,
		chainID,
	)

	// check the total power returned
	require.Equal(t, expTotalPower, res)
}

func TestIdentifyConsumerChainIDFromIBCPacket(t *testing.T) {
	var (
		chainID    = CONSUMER_CHAIN_ID
		ccvChannel = "channel-0"
	)

	testCases := []struct {
		name          string
		packet        channeltypes.Packet
		expectedCalls func(sdk.Context, testkeeper.MockedKeepers, channeltypes.Packet) []*gomock.Call
		expCCVChannel bool
		expErr        bool
	}{
		{
			"channel not found",
			channeltypes.NewPacket(
				[]byte{},
				0,
				"srcPort",
				"srcChannel",
				"dstPort",
				"dstChannel",
				clienttypes.NewHeight(1, 1),
				0,
			),
			func(ctx sdk.Context, mocks testkeeper.MockedKeepers, packet channeltypes.Packet) []*gomock.Call {
				return []*gomock.Call{
					mocks.MockChannelKeeper.EXPECT().GetChannel(
						ctx,
						packet.DestinationPort,
						packet.DestinationChannel,
					).Return(channeltypes.Channel{}, false).Times(1),
				}
			},
			false,
			true,
		},
		{
			"connection hops can't be greater than 1",
			channeltypes.NewPacket(
				[]byte{},
				0,
				"srcPort",
				"srcChannel",
				"dstPort",
				"dstChannel",
				clienttypes.NewHeight(1, 1),
				0,
			),
			func(ctx sdk.Context, mocks testkeeper.MockedKeepers, packet channeltypes.Packet) []*gomock.Call {
				return []*gomock.Call{
					mocks.MockChannelKeeper.EXPECT().GetChannel(
						ctx,
						packet.DestinationPort,
						packet.DestinationChannel,
					).Return(channeltypes.Channel{ConnectionHops: []string{"conn1", "conn2"}}, true).Times(1),
				}
			},
			false,
			true,
		},
		{
			"underlying client isn't found",
			channeltypes.NewPacket(
				[]byte{},
				0,
				"srcPort",
				"srcChannel",
				"dstPort",
				"dstChannel",
				clienttypes.NewHeight(1, 1),
				0,
			),
			func(ctx sdk.Context, mocks testkeeper.MockedKeepers, packet channeltypes.Packet) []*gomock.Call {
				return []*gomock.Call{
					mocks.MockChannelKeeper.EXPECT().GetChannel(
						ctx,
						packet.DestinationPort,
						packet.DestinationChannel,
					).Return(channeltypes.Channel{ConnectionHops: []string{"connectionID"}}, true).Times(1),
					mocks.MockConnectionKeeper.EXPECT().GetConnection(ctx, "connectionID").Return(
						conntypes.ConnectionEnd{ClientId: "clientID"}, true,
					).Times(1),
					mocks.MockClientKeeper.EXPECT().GetClientState(ctx, "clientID").Return(
						&ibctmtypes.ClientState{ChainId: ""}, false,
					).Times(1),
				}
			},
			false,
			true,
		},
		{
			"no CCV channel registered",
			channeltypes.NewPacket(
				[]byte{},
				0,
				"srcPort",
				"srcChannel",
				"dstPort",
				"dstChannel",
				clienttypes.NewHeight(1, 1),
				0,
			),
			func(ctx sdk.Context, mocks testkeeper.MockedKeepers, packet channeltypes.Packet) []*gomock.Call {
				return []*gomock.Call{
					mocks.MockChannelKeeper.EXPECT().GetChannel(
						ctx,
						packet.DestinationPort,
						packet.DestinationChannel,
					).Return(channeltypes.Channel{ConnectionHops: []string{"connectionID"}}, true).Times(1),
					mocks.MockConnectionKeeper.EXPECT().GetConnection(ctx, "connectionID").Return(
						conntypes.ConnectionEnd{ClientId: "clientID"}, true,
					).Times(1),
					mocks.MockClientKeeper.EXPECT().GetClientState(ctx, "clientID").Return(
						&ibctmtypes.ClientState{ChainId: chainID}, true,
					).Times(1),
				}
			},
			false,
			true,
		},
		{
			"consumer chain identified",
			channeltypes.NewPacket(
				[]byte{},
				0,
				"srcPort",
				"srcChannel",
				"dstPort",
				"dstChannel",
				clienttypes.NewHeight(1, 1),
				0,
			),
			func(ctx sdk.Context, mocks testkeeper.MockedKeepers, packet channeltypes.Packet) []*gomock.Call {
				return []*gomock.Call{
					mocks.MockChannelKeeper.EXPECT().GetChannel(
						ctx,
						packet.DestinationPort,
						packet.DestinationChannel,
					),
				}
			},
			false,
			true,
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			keeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
			defer ctrl.Finish()

			tc.expectedCalls(ctx, mocks, tc.packet)
			_, err := keeper.IdentifyConsumerIdFromIBCPacket(
				ctx,
				tc.packet,
			)

			if tc.expCCVChannel {
				keeper.SetConsumerIdToChannelId(ctx, chainID, ccvChannel)
			}

			if !tc.expErr {
				require.NoError(t, err)
			} else {
				require.Error(t, err)
			}
		})
	}
}

func TestIsEligibleForConsumerRewards(t *testing.T) {
	keeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	params := providertypes.DefaultParams()
	params.NumberOfEpochsToStartReceivingRewards = 10
	params.BlocksPerEpoch = 5
	keeper.SetParams(ctx, params)

	numberOfBlocks := params.NumberOfEpochsToStartReceivingRewards * params.BlocksPerEpoch

	require.False(t, keeper.IsEligibleForConsumerRewards(ctx.WithBlockHeight(numberOfBlocks-1), 0))
	require.True(t, keeper.IsEligibleForConsumerRewards(ctx.WithBlockHeight(numberOfBlocks), 0))
	require.True(t, keeper.IsEligibleForConsumerRewards(ctx.WithBlockHeight(numberOfBlocks+1), 0))
	require.True(t, keeper.IsEligibleForConsumerRewards(ctx.WithBlockHeight(numberOfBlocks+1), 1))
	require.False(t, keeper.IsEligibleForConsumerRewards(ctx.WithBlockHeight(numberOfBlocks+1), 2))
}

func TestChangeRewardDenoms(t *testing.T) {
	keeper, ctx, _, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))

	// Test adding a new denomination
	denomsToAdd := []string{"denom1"}
	denomsToRemove := []string{}
	attributes := keeper.ChangeRewardDenoms(ctx, denomsToAdd, denomsToRemove)

	require.Len(t, attributes, 1)
	require.Equal(t, providertypes.AttributeAddConsumerRewardDenom, attributes[0].Key)
	require.Equal(t, "denom1", attributes[0].Value)
	require.True(t, keeper.ConsumerRewardDenomExists(ctx, "denom1"))

	// Test adding a denomination that is already registered
	attributes = keeper.ChangeRewardDenoms(ctx, denomsToAdd, denomsToRemove)
	require.Len(t, attributes, 0) // No attributes should be returned since the denom is already registered

	// Test removing a registered denomination
	denomsToAdd = []string{}
	denomsToRemove = []string{"denom1"}
	attributes = keeper.ChangeRewardDenoms(ctx, denomsToAdd, denomsToRemove)

	require.Len(t, attributes, 1)
	require.Equal(t, providertypes.AttributeRemoveConsumerRewardDenom, attributes[0].Key)
	require.Equal(t, "denom1", attributes[0].Value)
	require.False(t, keeper.ConsumerRewardDenomExists(ctx, "denom1"))

	// Test removing a denomination that is not registered
	attributes = keeper.ChangeRewardDenoms(ctx, denomsToAdd, denomsToRemove)
	require.Len(t, attributes, 0) // No attributes should be returned since the denom is not registered
}

func TestHandleSetConsumerCommissionRate(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	providerAddr := providertypes.NewProviderConsAddress([]byte("providerAddr"))

	// trying to set a commission rate to a unknown consumer chain
	require.Error(t, providerKeeper.HandleSetConsumerCommissionRate(ctx, "unknownChainID", providerAddr, math.LegacyZeroDec()))

	// setup a pending consumer chain
	consumerId := "0"
	providerKeeper.FetchAndIncrementConsumerId(ctx)
	providerKeeper.SetConsumerPhase(ctx, consumerId, providertypes.CONSUMER_PHASE_INITIALIZED)

	// check that there's no commission rate set for the validator yet
	_, found := providerKeeper.GetConsumerCommissionRate(ctx, consumerId, providerAddr)
	require.False(t, found)

	mocks.MockStakingKeeper.EXPECT().MinCommissionRate(ctx).Return(math.LegacyZeroDec(), nil).Times(1)
	require.NoError(t, providerKeeper.HandleSetConsumerCommissionRate(ctx, consumerId, providerAddr, math.LegacyOneDec()))

	// check that the commission rate is now set
	cr, found := providerKeeper.GetConsumerCommissionRate(ctx, consumerId, providerAddr)
	require.Equal(t, math.LegacyOneDec(), cr)
	require.True(t, found)

	// set minimum rate of 1/2
	commissionRate := math.LegacyNewDec(1).Quo(math.LegacyNewDec(2))
	mocks.MockStakingKeeper.EXPECT().MinCommissionRate(ctx).Return(commissionRate, nil).AnyTimes()

	// try to set a rate slightly below the minimum
	require.Error(t, providerKeeper.HandleSetConsumerCommissionRate(
		ctx,
		consumerId,
		providerAddr,
		commissionRate.Sub(math.LegacyNewDec(1).Quo(math.LegacyNewDec(100)))), // 0.5 - 0.01
		"commission rate should be rejected (below min), but is not",
	)

	// set a valid commission equal to the minimum
	require.NoError(t, providerKeeper.HandleSetConsumerCommissionRate(ctx, consumerId, providerAddr, commissionRate))
	// check that the rate was set
	cr, found = providerKeeper.GetConsumerCommissionRate(ctx, consumerId, providerAddr)
	require.Equal(t, commissionRate, cr)
	require.True(t, found)
}

// TestAllowlistedRewardDenoms tests the `GetAllowlistedRewardDenoms`, `SetAllowlistedRewardDenom`,
// `UpdateAllowlistedRewardDenoms` and `DeleteAllowlistedRewardDenoms` methods.
func TestAllowlistedRewardDenoms(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerId := "0"
	denoms, err := providerKeeper.GetAllowlistedRewardDenoms(ctx, consumerId)
	require.Empty(t, denoms)
	require.NoError(t, err)

	denomsToSet := []string{"denom1", "denom2", "denom3"}
	providerKeeper.SetAllowlistedRewardDenoms(ctx, consumerId, denomsToSet)

	denoms, err = providerKeeper.GetAllowlistedRewardDenoms(ctx, consumerId)
	require.Equal(t, denomsToSet, denoms)
	require.NoError(t, err)

	updatedDenoms := []string{"updatedDenom1", "updatedDenom2"}
	err = providerKeeper.UpdateAllowlistedRewardDenoms(ctx, consumerId, updatedDenoms)
	require.NoError(t, err)
	denoms, err = providerKeeper.GetAllowlistedRewardDenoms(ctx, consumerId)
	require.Equal(t, updatedDenoms, denoms)
	require.NoError(t, err)

	providerKeeper.DeleteAllowlistedRewardDenoms(ctx, consumerId)
	denoms, err = providerKeeper.GetAllowlistedRewardDenoms(ctx, consumerId)
	require.Empty(t, denoms)
	require.NoError(t, err)
}

// TestConsumerRewardsAllocationByDenom tests the `*ConsumerRewardsAllocationByDenom* methods
func TestConsumerRewardsAllocationByDenom(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerId := "0"
	denom := "denom"
	rewards, err := providerKeeper.GetConsumerRewardsAllocationByDenom(ctx, consumerId, denom)
	require.Empty(t, rewards.Rewards)
	require.NoError(t, err)

	rewardAllocation := providertypes.ConsumerRewardsAllocation{
		Rewards: sdk.NewDecCoins(sdk.NewDecCoin("uatom", math.NewInt(1000))),
	}

	err = providerKeeper.SetConsumerRewardsAllocationByDenom(ctx, consumerId, denom, rewardAllocation)
	rewards, err = providerKeeper.GetConsumerRewardsAllocationByDenom(ctx, consumerId, denom)
	require.Equal(t, rewardAllocation, rewards)
	require.NoError(t, err)

	providerKeeper.DeleteConsumerRewardsAllocationByDenom(ctx, consumerId, denom)
	rewards, err = providerKeeper.GetConsumerRewardsAllocationByDenom(ctx, consumerId, denom)
	require.Empty(t, rewards.Rewards)
	require.NoError(t, err)
}
