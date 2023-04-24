package keeper

import (
	"context"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/x/ccv/consumer/types"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

var _ types.QueryServer = Keeper{}

func (k Keeper) QueryNextFeeDistribution(c context.Context,
	req *types.QueryNextFeeDistributionEstimateRequest,
) (*types.QueryNextFeeDistributionEstimateResponse, error) {
	ctx := sdk.UnwrapSDKContext(c)

	if req == nil {
		return nil, status.Errorf(codes.InvalidArgument, "empty request")
	}

	nextDist := k.GetEstimatedNextFeeDistribution(ctx)

	return &types.QueryNextFeeDistributionEstimateResponse{Data: &nextDist}, nil
}

func (k Keeper) QueryParams(c context.Context,
	req *types.QueryParamsRequest,
) (*types.QueryParamsResponse, error) {
	ctx := sdk.UnwrapSDKContext(c)

	if req == nil {
		return nil, status.Errorf(codes.InvalidArgument, "empty request")
	}

	p := k.GetConsumerParams(ctx)

	return &types.QueryParamsResponse{Params: p}, nil
}
