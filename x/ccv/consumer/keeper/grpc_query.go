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
	req *types.QueryNextFeeDistributionEstimateRequest) (*types.QueryNextFeeDistributionEstimateResponse, error) {

	ctx := sdk.UnwrapSDKContext(c)

	if req == nil {
		return nil, status.Errorf(codes.InvalidArgument, "empty request")
	}

	nextDist, err := k.GetEstimatedNextFeeDistribution(ctx)
	if err != nil {
		return nil, status.Errorf(codes.Internal, err.Error())
	}

	return &types.QueryNextFeeDistributionEstimateResponse{Data: &nextDist}, nil
}
