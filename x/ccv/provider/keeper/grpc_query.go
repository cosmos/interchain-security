package keeper

import (
	"context"

	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

var _ types.QueryServer = Keeper{}

func (k Keeper) ConsumerGenesis(c context.Context, req *types.QueryConsumerGenesisRequest) (*types.QueryConsumerGenesisResponse, error) {
	ctx := sdk.UnwrapSDKContext(c)

	if req == nil {
		return nil, status.Errorf(codes.InvalidArgument, "empty request")
	}

	if req.ChainId == "" {
		return nil, status.Errorf(codes.InvalidArgument, "invalid request: chain id cannot be empty")
	}

	gen, ok := k.GetConsumerGenesis(ctx, req.ChainId)
	if !ok {
		return nil, sdkerrors.Wrap(types.ErrUnknownConsumerChainId, req.ChainId)
	}

	return &types.QueryConsumerGenesisResponse{GenesisState: gen}, nil
}

func (k Keeper) ConsumerChains(goCtx context.Context, req *types.QueryConsumerChainsRequest) (*types.QueryConsumerChainsResponse, error) {
	if req == nil {
		return nil, status.Error(codes.InvalidArgument, "empty request")
	}

	ctx := sdk.UnwrapSDKContext(goCtx)
	chains := []string{}
	cb := func(ctx sdk.Context, chainID string) bool {
		chains = append(chains, chainID)
		return false
	}
	k.IterateConsumerChains(ctx, cb)

	return &types.QueryConsumerChainsResponse{ChainIds: chains}, nil
}
