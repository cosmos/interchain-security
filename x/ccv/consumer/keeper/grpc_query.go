package keeper

import (
	"context"

	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"

	sdk "github.com/cosmos/cosmos-sdk/types"

	"github.com/cosmos/interchain-security/v3/x/ccv/consumer/types"
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

	p, err := k.GetConsumerParams(ctx)
	if err != nil {
		return nil, status.Errorf(codes.NotFound, "no consumer parameters found")
	}

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
