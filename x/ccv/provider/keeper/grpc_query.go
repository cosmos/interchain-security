package keeper

import (
	"context"
	"fmt"

	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"

	errorsmod "cosmossdk.io/errors"

	sdk "github.com/cosmos/cosmos-sdk/types"

	"github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v3/x/ccv/types"
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
		return nil, errorsmod.Wrap(types.ErrUnknownConsumerChainId, req.ChainId)
	}

	return &types.QueryConsumerGenesisResponse{GenesisState: gen}, nil
}

func (k Keeper) QueryParams(goCtx context.Context, req *types.QueryParamsRequest) (*types.QueryParamsResponse, error) {
	if req == nil {
		return nil, status.Error(codes.InvalidArgument, "empty request")
	}

	ctx := sdk.UnwrapSDKContext(goCtx)
	params, err := k.GetParams(ctx)
	if err != nil {
		return nil, status.Error(codes.NotFound, "no parameters found")
	}
	return &types.QueryParamsResponse{Params: params}, nil
}

func (k Keeper) QueryConsumerChains(goCtx context.Context, req *types.QueryConsumerChainsRequest) (*types.QueryConsumerChainsResponse, error) {
	if req == nil {
		return nil, status.Error(codes.InvalidArgument, "empty request")
	}

	ctx := sdk.UnwrapSDKContext(goCtx)

	// convert to array of pointers
	chains := []*types.Chain{}
	for _, chain := range k.GetAllConsumerChains(ctx) {
		// prevent implicit memory aliasing
		c := chain
		chains = append(chains, &c)
	}

	return &types.QueryConsumerChainsResponse{Chains: chains}, nil
}

func (k Keeper) QueryConsumerChainStarts(goCtx context.Context, req *types.QueryConsumerChainStartProposalsRequest) (*types.QueryConsumerChainStartProposalsResponse, error) {
	if req == nil {
		return nil, status.Error(codes.InvalidArgument, "empty request")
	}

	ctx := sdk.UnwrapSDKContext(goCtx)
	var props []*types.ConsumerAdditionProposal

	for _, prop := range k.GetAllPendingConsumerAdditionProps(ctx) {
		// prevent implicit memory aliasing
		p := prop
		props = append(props, &p)
	}

	return &types.QueryConsumerChainStartProposalsResponse{Proposals: &types.ConsumerAdditionProposals{Pending: props}}, nil
}

func (k Keeper) QueryConsumerChainStops(goCtx context.Context, req *types.QueryConsumerChainStopProposalsRequest) (*types.QueryConsumerChainStopProposalsResponse, error) {
	if req == nil {
		return nil, status.Error(codes.InvalidArgument, "empty request")
	}

	ctx := sdk.UnwrapSDKContext(goCtx)
	var props []*types.ConsumerRemovalProposal
	for _, prop := range k.GetAllPendingConsumerRemovalProps(ctx) {
		// prevent implicit memory aliasing
		p := prop
		props = append(props, &p)
	}

	return &types.QueryConsumerChainStopProposalsResponse{Proposals: &types.ConsumerRemovalProposals{Pending: props}}, nil
}

func (k Keeper) QueryValidatorConsumerAddr(goCtx context.Context, req *types.QueryValidatorConsumerAddrRequest) (*types.QueryValidatorConsumerAddrResponse, error) {
	if req == nil {
		return nil, status.Error(codes.InvalidArgument, "empty request")
	}

	ctx := sdk.UnwrapSDKContext(goCtx)

	providerAddrTmp, err := sdk.ConsAddressFromBech32(req.ProviderAddress)
	if err != nil {
		return nil, err
	}
	providerAddr := types.NewProviderConsAddress(providerAddrTmp)

	consumerKey, found := k.GetValidatorConsumerPubKey(ctx, req.ChainId, providerAddr)
	if !found {
		return &types.QueryValidatorConsumerAddrResponse{}, nil
	}

	consumerAddr, err := ccvtypes.TMCryptoPublicKeyToConsAddr(consumerKey)
	if err != nil {
		return nil, err
	}

	return &types.QueryValidatorConsumerAddrResponse{
		ConsumerAddress: consumerAddr.String(),
	}, nil
}

func (k Keeper) QueryValidatorProviderAddr(goCtx context.Context, req *types.QueryValidatorProviderAddrRequest) (*types.QueryValidatorProviderAddrResponse, error) {
	if req == nil {
		return nil, status.Error(codes.InvalidArgument, "empty request")
	}

	ctx := sdk.UnwrapSDKContext(goCtx)

	consumerAddrTmp, err := sdk.ConsAddressFromBech32(req.ConsumerAddress)
	if err != nil {
		return nil, err
	}
	consumerAddr := types.NewConsumerConsAddress(consumerAddrTmp)

	providerAddr, found := k.GetValidatorByConsumerAddr(ctx, req.ChainId, consumerAddr)
	if !found {
		return &types.QueryValidatorProviderAddrResponse{}, nil
	}

	return &types.QueryValidatorProviderAddrResponse{
		ProviderAddress: providerAddr.String(),
	}, nil
}

func (k Keeper) QueryThrottleState(goCtx context.Context, req *types.QueryThrottleStateRequest) (*types.QueryThrottleStateResponse, error) {
	if req == nil {
		return nil, status.Error(codes.InvalidArgument, "empty request")
	}

	ctx := sdk.UnwrapSDKContext(goCtx)

	meter := k.GetSlashMeter(ctx)
	allowance := k.GetSlashMeterAllowance(ctx)
	candidate := k.GetSlashMeterReplenishTimeCandidate(ctx) // always UTC
	packets := []*types.ThrottledSlashPacket{}

	// iterate global slash entries from all consumer chains
	// and fetch corresponding SlashPacketData from the per-chain throttled packet data queue
	allGlobalEntries := k.GetAllGlobalSlashEntries(ctx)

	for _, entry := range allGlobalEntries {
		// Obtain slash packet data instance for the given global entry
		slashData, found := k.getSlashPacketData(ctx, entry.ConsumerChainID, entry.IbcSeqNum)
		if !found {
			// silently skip over invalid data
			continue
		}

		packets = append(packets, &types.ThrottledSlashPacket{
			GlobalEntry: entry,
			Data:        slashData,
		})
	}

	return &types.QueryThrottleStateResponse{
		SlashMeter:             meter.Int64(),
		SlashMeterAllowance:    allowance.Int64(),
		NextReplenishCandidate: candidate,
		Packets:                packets,
	}, nil
}

func (k Keeper) QueryThrottledConsumerPacketData(goCtx context.Context, req *types.QueryThrottledConsumerPacketDataRequest) (*types.QueryThrottledConsumerPacketDataResponse, error) {
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

	packetDataInstances := []types.ThrottledPacketDataWrapper{}
	_, _, rawOrderedData, _ := k.GetAllThrottledPacketData(ctx, req.ChainId)

	for _, raw := range rawOrderedData {
		switch data := raw.(type) {
		case ccvtypes.SlashPacketData:
			w := &types.ThrottledPacketDataWrapper_SlashPacket{SlashPacket: &data}
			packetDataInstances = append(packetDataInstances, types.ThrottledPacketDataWrapper{
				Data: w,
			})
		case ccvtypes.VSCMaturedPacketData:
			w := &types.ThrottledPacketDataWrapper_VscMaturedPacket{VscMaturedPacket: &data}
			packetDataInstances = append(packetDataInstances, types.ThrottledPacketDataWrapper{
				Data: w,
			})
		default:
			k.Logger(ctx).Error(fmt.Sprintf("unexpected packet data type: %T", data))
		}
	}

	return &types.QueryThrottledConsumerPacketDataResponse{
		ChainId:             req.ChainId,
		Size_:               k.GetThrottledPacketDataSize(ctx, req.ChainId),
		PacketDataInstances: packetDataInstances,
	}, nil
}

// getSlashPacketData fetches a slash packet data from the store using consumerChainId and ibcSeqNum (direct access)
// If the returned bytes do not unmarshal to SlashPacketData, the data is considered not found.
func (k Keeper) getSlashPacketData(ctx sdk.Context, consumerChainID string, ibcSeqNum uint64) (ccvtypes.SlashPacketData, bool) {
	store := k.storeService.OpenKVStore(ctx)
	bz, err := store.Get(types.ThrottledPacketDataKey(consumerChainID, ibcSeqNum))
	if err != nil || len(bz) == 0 {
		return ccvtypes.SlashPacketData{}, false
	}

	if bz[0] != slashPacketData {
		return ccvtypes.SlashPacketData{}, false
	}

	packet := ccvtypes.SlashPacketData{}
	err = packet.Unmarshal(bz[1:])
	if err != nil {
		// If the data cannot be unmarshaled, it is considered not found
		return ccvtypes.SlashPacketData{}, false
	}

	return packet, true
}

func (k Keeper) QueryRegisteredConsumerRewardDenoms(goCtx context.Context, req *types.QueryRegisteredConsumerRewardDenomsRequest) (*types.QueryRegisteredConsumerRewardDenomsResponse, error) {
	if req == nil {
		return nil, status.Error(codes.InvalidArgument, "empty request")
	}

	ctx := sdk.UnwrapSDKContext(goCtx)

	denoms := k.GetAllConsumerRewardDenoms(ctx)

	return &types.QueryRegisteredConsumerRewardDenomsResponse{
		Denoms: denoms,
	}, nil
}
