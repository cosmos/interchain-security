package keeper

import (
	"context"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/core"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

var _ core.ConsumerQueryServer = Keeper{}

func (k Keeper) QueryNextFeeDistribution(c context.Context,
	req *core.QueryNextFeeDistributionEstimateRequest,
) (*core.QueryNextFeeDistributionEstimateResponse, error) {
	ctx := sdk.UnwrapSDKContext(c)

	if req == nil {
		return nil, status.Errorf(codes.InvalidArgument, "empty request")
	}

	nextDist := k.GetEstimatedNextFeeDistribution(ctx)

	return &core.QueryNextFeeDistributionEstimateResponse{Data: &nextDist}, nil
}

func (k Keeper) QueryParams(c context.Context,
	req *core.QueryParamsRequest,
) (*core.QueryParamsResponse, error) {
	ctx := sdk.UnwrapSDKContext(c)

	if req == nil {
		return nil, status.Errorf(codes.InvalidArgument, "empty request")
	}

	p := k.GetConsumerParams(ctx)

	return &core.QueryParamsResponse{Params: p}, nil
}
