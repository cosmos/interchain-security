package keeper_test

import (
	"testing"

	abci "github.com/cometbft/cometbft/abci/types"
	tmtypes "github.com/cometbft/cometbft/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
	conntypes "github.com/cosmos/ibc-go/v7/modules/core/03-connection/types"
	channeltypes "github.com/cosmos/ibc-go/v7/modules/core/04-channel/types"
	ibctmtypes "github.com/cosmos/ibc-go/v7/modules/light-clients/07-tendermint"
	testkeeper "github.com/cosmos/interchain-security/v4/testutil/keeper"
	"github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"
)

func TestComputeConsumerTotalVotingPower(t *testing.T) {
	keeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	createVal := func(power int64) tmtypes.Validator {
		signer := tmtypes.NewMockPV()
		val := tmtypes.NewValidator(signer.PrivKey.PubKey(), power)
		return *val
	}

	chainID := "consumer"
	validatorsVotes := make([]abci.VoteInfo, 5)

	expTotalPower := int64(0)

	// create validators, opt them in and use them
	// to create block votes
	for i := 0; i < 5; i++ {
		val := createVal(int64(i))
		keeper.SetOptedIn(
			ctx,
			chainID,
			types.OptedInValidator{
				ProviderAddr: val.Address,
				BlockHeight:  ctx.BlockHeight(),
				Power:        val.VotingPower,
				PublicKey:    val.PubKey.Bytes(),
			},
		)

		validatorsVotes = append(
			validatorsVotes,
			abci.VoteInfo{
				Validator: abci.Validator{
					Address: val.Address,
					Power:   val.VotingPower,
				},
			},
		)

		expTotalPower += val.VotingPower
	}

	res := keeper.ComputeConsumerTotalVotingPower(
		ctx,
		chainID,
		validatorsVotes,
	)

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
