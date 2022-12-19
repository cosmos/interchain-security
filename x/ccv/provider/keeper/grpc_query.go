package keeper

import (
	"context"
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"
	sdktypes "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
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

// TODO: change to GlobalSlashEntries naming
func (k Keeper) QueryPendingSlashPackets(goCtx context.Context, req *types.QueryPendingSlashPacketsRequest) (*types.QueryPendingSlashPacketsResponse, error) {
	if req == nil {
		return nil, status.Error(codes.InvalidArgument, "empty request")
	}

	ctx := sdk.UnwrapSDKContext(goCtx)

	meter := k.GetSlashMeter(ctx)
	allowance := k.GetSlashMeterAllowance(ctx)
	lastTs := k.GetLastSlashMeterFullTime(ctx) // always UTC
	nextReplenishTs := lastTs.Add(k.GetSlashMeterReplenishPeriod(ctx))
	packets := []*types.ThrottledSlashPacket{}

	// iterate global slash entries from all consumer chains
	// and fetch corresponding SlashPacketData from the per-chain throttled packet data queue
	allGlobalEntries := k.GetAllGlobalSlashEntries(ctx)

	for _, entry := range allGlobalEntries {
		slashData, found := k.getSlashPacketForGlobalEntry(ctx, entry.ConsumerChainID, entry.IbcSeqNum)
		if !found {
			// silently skip over invalid data
			continue
		}

		packets = append(packets, &types.ThrottledSlashPacket{
			GlobalEntry: entry,
			Data:        slashData,
		})
	}

	return &types.QueryPendingSlashPacketsResponse{
		SlashMeter:          meter.Int64(),
		SlashMeterAllowance: allowance.Int64(),
		LastReplenish:       lastTs,
		NextReplenish:       nextReplenishTs,
		Packets:             packets,
	}, nil
}

// TODO: change to ThrottledPacketData naming
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

	packets := []types.PendingPacketWrapper{}
	_, _, rawOrderedData, _ := k.GetAllThrottledPacketData(ctx, req.ChainId)

	for _, raw := range rawOrderedData {
		switch data := raw.(type) {
		case ccvtypes.SlashPacketData:
			w := &types.PendingPacketWrapper_SlashPacket{SlashPacket: &data}
			packets = append(packets, types.PendingPacketWrapper{
				Data: w,
			})
		case ccvtypes.VSCMaturedPacketData:
			w := &types.PendingPacketWrapper_VscMaturedPacket{VscMaturedPacket: &data}
			packets = append(packets, types.PendingPacketWrapper{
				Data: w,
			})
		default:
			k.Logger(ctx).Error(fmt.Sprintf("unexpected packet data type: %T", data))
		}
	}

	return &types.QueryPendingConsumerPacketsResponse{
		ChainId: req.ChainId,
		Size_:   k.GetThrottledPacketDataSize(ctx, req.ChainId),
		Packets: packets,
	}, nil
}

// getSlashPacketForGlobalEntry fetches a slash packet data from the store using consumerChainId and ibcSeqNum
// If the packets is not SlashPacketData, it is considered not found.
func (k Keeper) getSlashPacketForGlobalEntry(ctx sdktypes.Context, consumerChainID string, ibcSeqNum uint64) (ccvtypes.SlashPacketData, bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(providertypes.ThrottledPacketDataKey(consumerChainID, ibcSeqNum))
	if len(bz) == 0 {
		return ccvtypes.SlashPacketData{}, false
	}

	if bz[0] != slashPacketData {
		return ccvtypes.SlashPacketData{}, false
	}

	packet := ccvtypes.SlashPacketData{}
	err := packet.Unmarshal(bz[1:])

	if err != nil {
		panic(fmt.Sprintf("failed to unmarshal pending packet data: %v", err))
	}

	return packet, true
}
