package keeper

import (
	"context"

	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"
	"github.com/cosmos/interchain-security/x/ccv/utils"
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
	cb := func(ctx sdk.Context, chainID, clientID string) (stop bool) {
		chains = append(chains, &types.Chain{
			ChainId:  chainID,
			ClientId: clientID,
		})
		return false // do not stop the iteration
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

func (k Keeper) QueryValidatorConsumerAddr(goCtx context.Context, req *types.QueryValidatorConsumerAddrRequest) (*types.QueryValidatorConsumerAddrResponse, error) {
	if req == nil {
		return nil, status.Error(codes.InvalidArgument, "empty request")
	}

	ctx := sdk.UnwrapSDKContext(goCtx)

	providerAddr, err := sdk.ConsAddressFromBech32(req.ProviderAddress)
	if err != nil {
		return nil, err
	}

	consumerKey, found := k.GetValidatorConsumerPubKey(ctx, req.ChainId, providerAddr)
	if !found {
		return &types.QueryValidatorConsumerAddrResponse{}, nil
	}

	return &types.QueryValidatorConsumerAddrResponse{
		ConsumerAddress: utils.TMCryptoPublicKeyToConsAddr(consumerKey).String(),
	}, nil
}

func (k Keeper) QueryValidatorProviderAddr(goCtx context.Context, req *types.QueryValidatorProviderAddrRequest) (*types.QueryValidatorProviderAddrResponse, error) {
	if req == nil {
		return nil, status.Error(codes.InvalidArgument, "empty request")
	}

	ctx := sdk.UnwrapSDKContext(goCtx)

	consumerAddr, err := sdk.ConsAddressFromBech32(req.ConsumerAddress)
	if err != nil {
		return nil, err
	}

	providerAddr, found := k.GetValidatorByConsumerAddr(ctx, req.ChainId, consumerAddr)
	if !found {
		return &types.QueryValidatorProviderAddrResponse{}, nil
	}

	return &types.QueryValidatorProviderAddrResponse{
		ProviderAddress: providerAddr.String(),
	}, nil
}

func (k Keeper) QueryPendingSlashPackets(goCtx context.Context, req *types.QueryPendingSlashPacketsRequest) (*types.QueryPendingSlashPacketsResponse, error) {
	if req == nil {
		return nil, status.Error(codes.InvalidArgument, "empty request")
	}

	ctx := sdk.UnwrapSDKContext(goCtx)

	meter := k.GetSlashMeter(ctx)
	allowance := k.GetSlashMeterAllowance(ctx)
	lastTs := k.GetLastSlashMeterFullTime(ctx) // always UTC
	packets := []*types.PendingSlashPacket{}

	// Iterate through ordered (by received time) slash packet entries from any consumer chain
	k.IteratePendingSlashPacketEntries(ctx, func(entry types.SlashPacketEntry) (stop bool) {
		slashPacket, found := k.GetPendingSlashPacketData(ctx, entry.ConsumerChainID, entry.IbcSeqNum)
		if !found {
			// TODO: maybe error if package was not found?
			// I don't want to panic on provider in case of incomplete response data
			// don't stop on error
			return false
		}

		packets = append(packets, &types.PendingSlashPacket{
			ChainId:    entry.ConsumerChainID,
			ReceivedAt: entry.RecvTime,
			Data:       slashPacket,
		})
		return false
	})

	return &types.QueryPendingSlashPacketsResponse{
		SlashMeter:          meter.Int64(),
		SlashMeterAllowance: allowance.Int64(),
		LastReplenish:       lastTs,
		Packets:             packets,
	}, nil
}

func (k Keeper) QueryPendingConsumerPackets(goCtx context.Context, req *types.QueryPendingConsumerPacketsRequest) (*types.QueryPendingConsumerPacketsResponse, error) {
	if req == nil {
		return nil, status.Error(codes.InvalidArgument, "empty request")
	}

	if req.ChainId == "" {
		return nil, status.Error(codes.InvalidArgument, "invalid chain-id")
	}

	ctx := sdk.UnwrapSDKContext(goCtx)
	if _, found := k.GetChainToChannel(ctx, req.ChainId); !found {
		return nil, status.Error(codes.InvalidArgument, "invalid chain-id")
	}

	// TODO: maybe just dump it as JSON bytes?
	packets := []types.PendingPacketWrapper{}
	k.IteratePendingPacketData(ctx, req.ChainId, func(ibcSeqNum uint64, data interface{}) (stop bool) {
		switch data := data.(type) {
		case ccvtypes.SlashPacketData:
			packets = append(packets, types.PendingPacketWrapper{
				Data: &types.PendingPacketWrapper_SlashPacket{SlashPacket: &data},
			})
		case ccvtypes.VSCMaturedPacketData:
			packets = append(packets, types.PendingPacketWrapper{
				Data: &types.PendingPacketWrapper_VscMaturedPacket{VscMaturedPacket: &data},
			})
		default:
			// silently skip over invalid data
			return false

		}
		return false
	})

	return &types.QueryPendingConsumerPacketsResponse{
		ChainId: req.ChainId,
		Size_:   k.GetPendingPacketDataSize(ctx, req.ChainId),
		Packets: packets,
	}, nil
}
