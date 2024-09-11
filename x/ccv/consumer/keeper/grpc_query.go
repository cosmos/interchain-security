package keeper

import (
	"context"

	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"

	sdk "github.com/cosmos/cosmos-sdk/types"

	"github.com/cosmos/interchain-security/v6/x/ccv/consumer/types"
	ccvtypes "github.com/cosmos/interchain-security/v6/x/ccv/types"
)

var _ types.QueryServer = Keeper{} //nolint:golint

func (k Keeper) QueryNextFeeDistribution(c context.Context, //nolint:golint
	req *types.QueryNextFeeDistributionEstimateRequest,
) (*types.QueryNextFeeDistributionEstimateResponse, error) {
	ctx := sdk.UnwrapSDKContext(c)

	if req == nil {
		return nil, status.Errorf(codes.InvalidArgument, "empty request")
	}

	nextDist := k.GetEstimatedNextFeeDistribution(ctx)

	return &types.QueryNextFeeDistributionEstimateResponse{Data: &nextDist}, nil
}

func (k Keeper) QueryParams(c context.Context, //nolint:golint
	req *types.QueryParamsRequest,
) (*types.QueryParamsResponse, error) {
	ctx := sdk.UnwrapSDKContext(c)

	if req == nil {
		return nil, status.Errorf(codes.InvalidArgument, "empty request")
	}

	p := k.GetConsumerParams(ctx)

	return &types.QueryParamsResponse{Params: p}, nil
}

func (k Keeper) QueryProviderInfo(c context.Context, //nolint:golint
	req *types.QueryProviderInfoRequest,
) (*types.QueryProviderInfoResponse, error) {
	ctx := sdk.UnwrapSDKContext(c)
	if req == nil {
		return nil, status.Errorf(codes.InvalidArgument, "empty request")
	}

	return k.GetProviderInfo(ctx)
}

func (k Keeper) QueryThrottleState(c context.Context,
	req *types.QueryThrottleStateRequest,
) (*types.QueryThrottleStateResponse, error) {
	ctx := sdk.UnwrapSDKContext(c)

	resp := types.QueryThrottleStateResponse{}

	slashRecord, found := k.GetSlashRecord(ctx)
	if found {
		resp.SlashRecord = &slashRecord
	} else {
		resp.SlashRecord = nil
	}

	resp.PacketDataQueue = make([]ccvtypes.ConsumerPacketData, 0)
	pendingPackets := k.GetAllPendingPacketsWithIdx(ctx)
	for _, packet := range pendingPackets {
		resp.PacketDataQueue = append(resp.PacketDataQueue, packet.ConsumerPacketData)
	}
	return &resp, nil
}
