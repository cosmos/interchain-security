package keeper

import (
	"context"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/x/ccv/adminmodule/types"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

func (k Keeper) Admins(goCtx context.Context, req *types.QueryAdminsRequest) (*types.QueryAdminsResponse, error) {
	if req == nil {
		return nil, status.Error(codes.InvalidArgument, "invalid request")
	}

	return &types.QueryAdminsResponse{
		Admins: k.GetAdmins(sdk.UnwrapSDKContext(goCtx)),
	}, nil
}
