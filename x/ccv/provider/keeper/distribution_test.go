package keeper_test

import (
	"testing"

	"cosmossdk.io/math"
	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
	conntypes "github.com/cosmos/ibc-go/v8/modules/core/03-connection/types"
	channeltypes "github.com/cosmos/ibc-go/v8/modules/core/04-channel/types"
	ibctmtypes "github.com/cosmos/ibc-go/v8/modules/light-clients/07-tendermint"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"

	sdk "github.com/cosmos/cosmos-sdk/types"

	tmtypes "github.com/cometbft/cometbft/types"

	testkeeper "github.com/cosmos/interchain-security/v5/testutil/keeper"
	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	providertypes "github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
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

	chainID := "consumer"
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
		keeper.SetConsumerValidator(
			ctx,
			chainID,
			types.ConsumerValidator{
				ProviderConsAddr: val.Address,
				Power:            val.VotingPower,
			},
		)

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
		chainID    = "consumer"
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
			_, err := keeper.IdentifyConsumerChainIDFromIBCPacket(
				ctx,
				tc.packet,
			)

			if tc.expCCVChannel {
				keeper.SetChainToChannel(ctx, chainID, ccvChannel)
			}

			if !tc.expErr {
				require.NoError(t, err)
			} else {
				require.Error(t, err)
			}
		})
	}
}

func TestSetConsumerRewardsAllocation(t *testing.T) {
	keeperParams := testkeeper.NewInMemKeeperParams(t)
	ctx := keeperParams.Ctx

	ctrl := gomock.NewController(t)
	defer ctrl.Finish()
	mocks := testkeeper.NewMockedKeepers(ctrl)
	providerKeeper := testkeeper.NewInMemProviderKeeper(keeperParams, mocks)

	rewardAllocation := providertypes.ConsumerRewardsAllocation{
		Rewards: sdk.NewDecCoins(sdk.NewDecCoin("uatom", math.NewInt(1000))),
	}

	providerKeeper.SetConsumerRewardsAllocation(ctx, "consumer-1", rewardAllocation)

	alloc := providerKeeper.GetConsumerRewardsAllocation(ctx, "consumer-1")
	require.Equal(t, rewardAllocation, alloc)
}

func TestGetConsumerRewardsAllocationNil(t *testing.T) {
	keeperParams := testkeeper.NewInMemKeeperParams(t)
	ctx := keeperParams.Ctx

	ctrl := gomock.NewController(t)
	defer ctrl.Finish()
	mocks := testkeeper.NewMockedKeepers(ctrl)
	providerKeeper := testkeeper.NewInMemProviderKeeper(keeperParams, mocks)

	alloc := providerKeeper.GetConsumerRewardsAllocation(ctx, "consumer-1")

	expectedRewardAllocation := providertypes.ConsumerRewardsAllocation{
		Rewards: nil,
	}
	require.Equal(t, expectedRewardAllocation, alloc)
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
