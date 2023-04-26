package keeper

import (
	"context"
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	ccvtypes "github.com/cosmos/interchain-security/core"
	providertypes "github.com/cosmos/interchain-security/x/provider/types"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

var _ ccvtypes.ProviderQueryServer = Keeper{}

func (k Keeper) QueryConsumerGenesis(c context.Context, req *ccvtypes.QueryConsumerGenesisRequest) (*ccvtypes.QueryConsumerGenesisResponse, error) {
	ctx := sdk.UnwrapSDKContext(c)

	if req == nil {
		return nil, status.Errorf(codes.InvalidArgument, "empty request")
	}

	if req.ChainId == "" {
		return nil, status.Errorf(codes.InvalidArgument, "invalid request: chain id cannot be empty")
	}

	gen, ok := k.GetConsumerGenesis(ctx, req.ChainId)
	if !ok {
		return nil, sdkerrors.Wrap(ccvtypes.ErrUnknownConsumerChainId, req.ChainId)
	}

	return &ccvtypes.QueryConsumerGenesisResponse{GenesisState: gen}, nil
}

func (k Keeper) QueryConsumerChains(goCtx context.Context, req *ccvtypes.QueryConsumerChainsRequest) (*ccvtypes.QueryConsumerChainsResponse, error) {
	if req == nil {
		return nil, status.Error(codes.InvalidArgument, "empty request")
	}

	ctx := sdk.UnwrapSDKContext(goCtx)

	// convert to array of pointers
	chains := []*ccvtypes.Chain{}
	for _, chain := range k.GetAllConsumerChains(ctx) {
		// prevent implicit memory aliasing
		c := chain
		chains = append(chains, &c)
	}

	return &ccvtypes.QueryConsumerChainsResponse{Chains: chains}, nil
}

func (k Keeper) QueryConsumerChainStarts(goCtx context.Context, req *ccvtypes.QueryConsumerChainStartProposalsRequest) (*ccvtypes.QueryConsumerChainStartProposalsResponse, error) {
	if req == nil {
		return nil, status.Error(codes.InvalidArgument, "empty request")
	}

	ctx := sdk.UnwrapSDKContext(goCtx)
	var props []*ccvtypes.ConsumerAdditionProposal

	for _, prop := range k.GetAllPendingConsumerAdditionProps(ctx) {
		// prevent implicit memory aliasing
		p := prop
		props = append(props, &p)
	}

	return &ccvtypes.QueryConsumerChainStartProposalsResponse{Proposals: &ccvtypes.ConsumerAdditionProposals{Pending: props}}, nil
}

func (k Keeper) QueryConsumerChainStops(goCtx context.Context, req *ccvtypes.QueryConsumerChainStopProposalsRequest) (*ccvtypes.QueryConsumerChainStopProposalsResponse, error) {
	if req == nil {
		return nil, status.Error(codes.InvalidArgument, "empty request")
	}

	ctx := sdk.UnwrapSDKContext(goCtx)
	var props []*ccvtypes.ConsumerRemovalProposal
	for _, prop := range k.GetAllPendingConsumerRemovalProps(ctx) {
		// prevent implicit memory aliasing
		p := prop
		props = append(props, &p)
	}

	return &ccvtypes.QueryConsumerChainStopProposalsResponse{Proposals: &ccvtypes.ConsumerRemovalProposals{Pending: props}}, nil
}

func (k Keeper) QueryValidatorConsumerAddr(goCtx context.Context, req *ccvtypes.QueryValidatorConsumerAddrRequest) (*ccvtypes.QueryValidatorConsumerAddrResponse, error) {
	if req == nil {
		return nil, status.Error(codes.InvalidArgument, "empty request")
	}

	ctx := sdk.UnwrapSDKContext(goCtx)

	providerAddrTmp, err := sdk.ConsAddressFromBech32(req.ProviderAddress)
	if err != nil {
		return nil, err
	}
	providerAddr := ccvtypes.NewProviderConsAddress(providerAddrTmp)

	consumerKey, found := k.GetValidatorConsumerPubKey(ctx, req.ChainId, providerAddr)
	if !found {
		return &ccvtypes.QueryValidatorConsumerAddrResponse{}, nil
	}

	consumerAddr, err := ccvtypes.TMCryptoPublicKeyToConsAddr(consumerKey)
	if err != nil {
		return nil, err
	}

	return &ccvtypes.QueryValidatorConsumerAddrResponse{
		ConsumerAddress: consumerAddr.String(),
	}, nil
}

func (k Keeper) QueryValidatorProviderAddr(goCtx context.Context, req *ccvtypes.QueryValidatorProviderAddrRequest) (*ccvtypes.QueryValidatorProviderAddrResponse, error) {
	if req == nil {
		return nil, status.Error(codes.InvalidArgument, "empty request")
	}

	ctx := sdk.UnwrapSDKContext(goCtx)

	consumerAddrTmp, err := sdk.ConsAddressFromBech32(req.ConsumerAddress)
	if err != nil {
		return nil, err
	}
	consumerAddr := ccvtypes.NewConsumerConsAddress(consumerAddrTmp)

	providerAddr, found := k.GetValidatorByConsumerAddr(ctx, req.ChainId, consumerAddr)
	if !found {
		return &ccvtypes.QueryValidatorProviderAddrResponse{}, nil
	}

	return &ccvtypes.QueryValidatorProviderAddrResponse{
		ProviderAddress: providerAddr.String(),
	}, nil
}

func (k Keeper) QueryThrottleState(goCtx context.Context, req *ccvtypes.QueryThrottleStateRequest) (*ccvtypes.QueryThrottleStateResponse, error) {
	if req == nil {
		return nil, status.Error(codes.InvalidArgument, "empty request")
	}

	ctx := sdk.UnwrapSDKContext(goCtx)

	meter := k.GetSlashMeter(ctx)
	allowance := k.GetSlashMeterAllowance(ctx)
	candidate := k.GetSlashMeterReplenishTimeCandidate(ctx) // always UTC
	packets := []*ccvtypes.ThrottledSlashPacket{}

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

		packets = append(packets, &ccvtypes.ThrottledSlashPacket{
			GlobalEntry: entry,
			Data:        slashData,
		})
	}

	return &ccvtypes.QueryThrottleStateResponse{
		SlashMeter:             meter.Int64(),
		SlashMeterAllowance:    allowance.Int64(),
		NextReplenishCandidate: candidate,
		Packets:                packets,
	}, nil
}

func (k Keeper) QueryThrottledConsumerPacketData(goCtx context.Context, req *ccvtypes.QueryThrottledConsumerPacketDataRequest) (*ccvtypes.QueryThrottledConsumerPacketDataResponse, error) {
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

	packetDataInstances := []ccvtypes.ThrottledPacketDataWrapper{}
	_, _, rawOrderedData, _ := k.GetAllThrottledPacketData(ctx, req.ChainId)

	for _, raw := range rawOrderedData {
		switch data := raw.(type) {
		case ccvtypes.SlashPacketData:
			w := &ccvtypes.ThrottledPacketDataWrapper_SlashPacket{SlashPacket: &data}
			packetDataInstances = append(packetDataInstances, ccvtypes.ThrottledPacketDataWrapper{
				Data: w,
			})
		case ccvtypes.VSCMaturedPacketData:
			w := &ccvtypes.ThrottledPacketDataWrapper_VscMaturedPacket{VscMaturedPacket: &data}
			packetDataInstances = append(packetDataInstances, ccvtypes.ThrottledPacketDataWrapper{
				Data: w,
			})
		default:
			k.Logger(ctx).Error(fmt.Sprintf("unexpected packet data type: %T", data))
		}
	}

	return &ccvtypes.QueryThrottledConsumerPacketDataResponse{
		ChainId:             req.ChainId,
		Size_:               k.GetThrottledPacketDataSize(ctx, req.ChainId),
		PacketDataInstances: packetDataInstances,
	}, nil
}

// getSlashPacketData fetches a slash packet data from the store using consumerChainId and ibcSeqNum (direct access)
// If the returned bytes do not unmarshal to SlashPacketData, the data is considered not found.
func (k Keeper) getSlashPacketData(ctx sdk.Context, consumerChainID string, ibcSeqNum uint64) (ccvtypes.SlashPacketData, bool) {
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
		// If the data cannot be unmarshaled, it is considered not found
		return ccvtypes.SlashPacketData{}, false
	}

	return packet, true
}
