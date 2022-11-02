package keeper

import (
	"context"

	sdkcodectypes "github.com/cosmos/cosmos-sdk/codec/types"
	sdkcryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
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
		return false
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

func (k Keeper) QueryConsumerChainValidatorKeyAssignmentping(goCtx context.Context, req *types.QueryConsumerChainValidatorKeyAssignmentpingRequest) (*types.QueryConsumerChainValidatorKeyAssignmentpingResponse, error) {
	if req == nil {
		return nil, status.Error(codes.InvalidArgument, "empty request")
	}

	ctx := sdk.UnwrapSDKContext(goCtx)

	if _, found := k.GetConsumerClientId(ctx, req.ChainId); !found {
		return nil, types.ErrNoConsumerChainFound
	}

	providerValidatorAddr, err := sdk.ValAddressFromBech32(req.ProviderValidatorAddress)
	if err != nil {
		return nil, err
	}

	validator, found := k.stakingKeeper.GetValidator(ctx, providerValidatorAddr)
	if !found {
		return nil, types.ErrNoValidatorFound
	}

	providerTMPublicKey, err := validator.TmConsPublicKey()
	if err != nil {
		return nil, err
	}

	consumerTMPublicKey, found := k.KeyAssignment(ctx, req.ChainId).GetCurrentConsumerPubKeyFromProviderPubKey(providerTMPublicKey)
	if !found {
		return nil, types.ErrNoAssignedConsumerKeyFoundForValidator
	}

	consumerSDKPublicKey, err := sdkcryptocodec.FromTmProtoPublicKey(consumerTMPublicKey)
	if err != nil {
		return nil, err
	}

	var pubKeyAny *sdkcodectypes.Any
	if consumerSDKPublicKey != nil {
		var err error
		if pubKeyAny, err = sdkcodectypes.NewAnyWithValue(consumerSDKPublicKey); err != nil {
			return nil, err
		}
	} else {
		// TODO: improve err info
		return nil, types.ErrInvalidValidatorPubKey
	}

	if pubKeyAny == nil {
		// TODO: improve err info
		return nil, types.ErrInvalidValidatorPubKey
	}

	return &types.QueryConsumerChainValidatorKeyAssignmentpingResponse{
		ConsumerValidatorPubKey: pubKeyAny,
	}, nil
}
