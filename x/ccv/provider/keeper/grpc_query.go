package keeper

import (
	"context"

	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	utils "github.com/cosmos/interchain-security/x/ccv/utils"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

var _ types.QueryServer = Keeper{}

func (k Keeper) QueryConsumerGenesis(c context.Context, req *types.QueryConsumerGenesisRequest) (*types.QueryConsumerGenesisResponse, error) {
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

func (k Keeper) QueryConsumerChains(goCtx context.Context, req *types.QueryConsumerChainsRequest) (*types.QueryConsumerChainsResponse, error) {
	if req == nil {
		return nil, status.Error(codes.InvalidArgument, "empty request")
	}

	ctx := sdk.UnwrapSDKContext(goCtx)
	chains := []*types.Chain{}
	cb := func(ctx sdk.Context, chainID, clientID string) bool {
		chains = append(chains, &types.Chain{
			ChainId:  chainID,
			ClientId: clientID,
		})
		return true
	}
	k.IterateConsumerChains(ctx, cb)

	return &types.QueryConsumerChainsResponse{Chains: chains}, nil
}

func (k Keeper) QueryConsumerChainStarts(goCtx context.Context, req *types.QueryConsumerChainStartProposalsRequest) (*types.QueryConsumerChainStartProposalsResponse, error) {
	if req == nil {
		return nil, status.Error(codes.InvalidArgument, "empty request")
	}

	ctx := sdk.UnwrapSDKContext(goCtx)
	props := k.GetAllConsumerAdditionProps(ctx)

	return &types.QueryConsumerChainStartProposalsResponse{Proposals: &props}, nil
}

func (k Keeper) QueryConsumerChainStops(goCtx context.Context, req *types.QueryConsumerChainStopProposalsRequest) (*types.QueryConsumerChainStopProposalsResponse, error) {
	if req == nil {
		return nil, status.Error(codes.InvalidArgument, "empty request")
	}

	ctx := sdk.UnwrapSDKContext(goCtx)
	props := k.GetAllConsumerRemovalProps(ctx)

	return &types.QueryConsumerChainStopProposalsResponse{Proposals: &props}, nil
}

func (k Keeper) QueryAssignedConsumerAddr(goCtx context.Context, req *types.QueryAssignedConsumerAddrRequest) (*types.QueryAssignedConsumerAddrResponse, error) {
	if req == nil {
		return nil, status.Error(codes.InvalidArgument, "empty request")
	}

	ctx := sdk.UnwrapSDKContext(goCtx)

	if _, found := k.GetConsumerClientId(ctx, req.ChainId); !found {
		return nil, types.ErrUnknownConsumerChainId
	}

	providerAddr, err := sdk.ConsAddressFromBech32(req.ProviderAddress)
	if err != nil {
		return nil, err
	}

	consumerKey, found := k.GetConsumerKey(ctx, req.ChainId, providerAddr)
	if !found {
		return nil, types.ErrNoAssignedConsumerAddress
	}

	return &types.QueryAssignedConsumerAddrResponse{
		ConsumerAddress: utils.TMCryptoPublicKeyToConsAddr(consumerKey).String(),
	}, nil
}

func (k Keeper) QueryAssignedProviderAddr(goCtx context.Context, req *types.QueryAssignedProviderAddrRequest) (*types.QueryAssignedProviderAddrResponse, error) {
	if req == nil {
		return nil, status.Error(codes.InvalidArgument, "empty request")
	}

	ctx := sdk.UnwrapSDKContext(goCtx)

	if _, found := k.GetConsumerClientId(ctx, req.ChainId); !found {
		return nil, types.ErrUnknownConsumerChainId
	}

	consumerAddr, err := sdk.ConsAddressFromBech32(req.ConsumerAddress)
	if err != nil {
		return nil, err
	}

	providerAddr, found := k.GetValidatorByConsumerAddr(ctx, req.ChainId, consumerAddr)
	if !found {
		return nil, types.ErrNoAssignedProviderAddress
	}

	return &types.QueryAssignedProviderAddrResponse{
		ProviderAddress: providerAddr.String(),
	}, nil
}
