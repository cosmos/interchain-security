package keeper

import (
	"context"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"

	"github.com/octopus-network/interchain-security/x/ccv/consumer/types"
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

	p := k.GetParams(ctx)

	return &types.QueryParamsResponse{Params: p}, nil
}
