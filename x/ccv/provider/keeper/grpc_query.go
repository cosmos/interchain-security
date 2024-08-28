package keeper

import (
	"context"
	"fmt"
	"strconv"

	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"

	errorsmod "cosmossdk.io/errors"

	sdk "github.com/cosmos/cosmos-sdk/types"

	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v5/x/ccv/types"
)

var _ types.QueryServer = Keeper{}

func (k Keeper) QueryConsumerGenesis(c context.Context, req *types.QueryConsumerGenesisRequest) (*types.QueryConsumerGenesisResponse, error) {
	ctx := sdk.UnwrapSDKContext(c)

	if req == nil {
		return nil, status.Errorf(codes.InvalidArgument, "empty request")
	} else if req.ChainId != "" {
		return nil, status.Errorf(codes.InvalidArgument, "ChainId has been deprecated. Use ConsumerId instead.")
	}

	consumerId := req.ConsumerId
	if err := types.ValidateConsumerId(consumerId); err != nil {
		return nil, status.Error(codes.InvalidArgument, errorsmod.Wrap(types.ErrInvalidConsumerId, consumerId).Error())
	}

	gen, ok := k.GetConsumerGenesis(ctx, consumerId)
	if !ok {
		return nil, status.Error(
			codes.NotFound,
			errorsmod.Wrap(types.ErrUnknownConsumerId, consumerId).Error(),
		)
	}

	return &types.QueryConsumerGenesisResponse{GenesisState: gen}, nil
}

func (k Keeper) QueryConsumerChains(goCtx context.Context, req *types.QueryConsumerChainsRequest) (*types.QueryConsumerChainsResponse, error) {
	if req == nil {
		return nil, status.Error(codes.InvalidArgument, "empty request")
	}

	ctx := sdk.UnwrapSDKContext(goCtx)

	lastCID, ok := k.GetConsumerId(ctx)
	if !ok {
		return &types.QueryConsumerChainsResponse{}, nil
	}

	consumerIds := []string{}
	phase := ConsumerPhase(byte(req.Phase))

	switch {
	case phase == Launched:
		consumerIds = append(consumerIds, k.GetAllRegisteredConsumerIds(ctx)...)
	case phase == Initialized:
		consumerIds = append(consumerIds, k.GetInitializedConsumers(ctx)...)
	case phase == Registered || phase == FailedToLaunch || phase == Stopped:
		for i := uint64(0); i <= lastCID; i++ {
			p, ok := k.GetConsumerPhase(ctx, strconv.FormatInt(int64(i), 10))
			if !ok {
				return nil, status.Error(codes.Internal, fmt.Sprintf("cannot retrieve phase for consumer id: %d", phase))
			}
			if p == phase {
				consumerIds = append(consumerIds, strconv.FormatInt(int64(i), 10))
			}
		}

	default:
		return nil, status.Error(codes.InvalidArgument, fmt.Sprintf("invalid consumer phase %v", phase))
	}

	chains := make([]*types.Chain, len(consumerIds))
	for i, cID := range consumerIds {
		c, err := k.GetConsumerChain(ctx, cID)
		if err != nil {
			return nil, status.Error(codes.Internal, err.Error())
		}
		chains[i] = &c
	}

	return &types.QueryConsumerChainsResponse{Chains: chains}, nil
}

// GetConsumerChain returns a Chain data structure with all the necessary fields
func (k Keeper) GetConsumerChain(ctx sdk.Context, consumerId string) (types.Chain, error) {
	// Get the minimal power in the top N for the consumer chain
	minPowerInTopN, found := k.GetMinimumPowerInTopN(ctx, consumerId)
	if !found {
		k.Logger(ctx).Error("failed to get minimum power in top N, treating as -1", "chain", consumerId)
		minPowerInTopN = -1
	}

	chainID, err := k.GetConsumerChainId(ctx, consumerId)
	if err != nil {
		return types.Chain{}, fmt.Errorf("cannot find chain ID for consumer (%s):%s", consumerId, err)
	}

	clientId, _ := k.GetConsumerClientId(ctx, consumerId)

	phase, ok := k.GetConsumerPhase(ctx, consumerId)
	if !ok {
		return types.Chain{}, fmt.Errorf("cannot find phase for consumer (%s)", consumerId)
	}

	allowlist := k.GetAllowList(ctx, consumerId)
	strAllowlist := make([]string, len(allowlist))
	for i, addr := range allowlist {
		strAllowlist[i] = addr.String()
	}

	denylist := k.GetDenyList(ctx, consumerId)
	strDenylist := make([]string, len(denylist))
	for i, addr := range denylist {
		strDenylist[i] = addr.String()
	}

	metadata, err := k.GetConsumerMetadata(ctx, consumerId)
	if err != nil {
		return types.Chain{}, fmt.Errorf("cannot get metadata for consumer (%s): %w", consumerId, err)
	}

	return types.Chain{
		ChainId:            chainID,
		ClientId:           clientId,
		Top_N:              k.GetTopN(ctx, consumerId),
		MinPowerInTop_N:    minPowerInTopN,
		ValidatorSetCap:    k.GetValidatorSetCap(ctx, consumerId),
		ValidatorsPowerCap: k.GetValidatorsPowerCap(ctx, consumerId),
		Allowlist:          strAllowlist,
		Denylist:           strDenylist,
		Phase:              uint32(phase),
		Metadata:           metadata,
	}, nil
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
		return nil, status.Errorf(codes.InvalidArgument, "empty request")
	} else if req.ChainId != "" {
		return nil, status.Errorf(codes.InvalidArgument, "ChainId has been deprecated. Use ConsumerId instead.")
	}

	ctx := sdk.UnwrapSDKContext(goCtx)

	consumerId := req.ConsumerId
	if err := types.ValidateConsumerId(consumerId); err != nil {
		return nil, status.Error(codes.InvalidArgument, errorsmod.Wrap(types.ErrInvalidConsumerId, consumerId).Error())
	}

	providerAddrTmp, err := sdk.ConsAddressFromBech32(req.ProviderAddress)
	if err != nil {
		return nil, err
	}
	providerAddr := types.NewProviderConsAddress(providerAddrTmp)

	consumerKey, found := k.GetValidatorConsumerPubKey(ctx, consumerId, providerAddr)
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
		return nil, status.Errorf(codes.InvalidArgument, "empty request")
	} else if req.ChainId != "" {
		return nil, status.Errorf(codes.InvalidArgument, "ChainId has been deprecated. Use ConsumerId instead.")
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

	return &types.QueryThrottleStateResponse{
		SlashMeter:             meter.Int64(),
		SlashMeterAllowance:    allowance.Int64(),
		NextReplenishCandidate: candidate,
	}, nil
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

func (k Keeper) QueryProposedConsumerChainIDs(goCtx context.Context, req *types.QueryProposedChainIDsRequest) (*types.QueryProposedChainIDsResponse, error) {
	if req == nil {
		return nil, status.Error(codes.InvalidArgument, "empty request")
	}

	ctx := sdk.UnwrapSDKContext(goCtx)

	chains := k.GetAllProposedConsumerChainIDs(ctx)

	return &types.QueryProposedChainIDsResponse{
		ProposedChains: chains,
	}, nil
}

func (k Keeper) QueryAllPairsValConAddrByConsumerChainID(goCtx context.Context, req *types.QueryAllPairsValConAddrByConsumerChainIDRequest) (*types.QueryAllPairsValConAddrByConsumerChainIDResponse, error) {
	if req == nil {
		return nil, status.Errorf(codes.InvalidArgument, "empty request")
	} else if req.ChainId != "" {
		return nil, status.Errorf(codes.InvalidArgument, "ChainId has been deprecated. Use ConsumerId instead.")
	}

	consumerId := req.ConsumerId
	if err := types.ValidateConsumerId(consumerId); err != nil {
		return nil, status.Error(codes.InvalidArgument, errorsmod.Wrap(types.ErrInvalidConsumerId, consumerId).Error())
	}

	// list of pairs valconsensus addr <providerValConAddrs : consumerValConAddrs>
	pairValConAddrs := []*types.PairValConAddrProviderAndConsumer{}

	ctx := sdk.UnwrapSDKContext(goCtx)
	validatorConsumerPubKeys := k.GetAllValidatorConsumerPubKeys(ctx, &consumerId)
	for _, data := range validatorConsumerPubKeys {
		consumerAddr, err := ccvtypes.TMCryptoPublicKeyToConsAddr(*data.ConsumerKey)
		if err != nil {
			return nil, err
		}
		pairValConAddrs = append(pairValConAddrs, &types.PairValConAddrProviderAndConsumer{
			ProviderAddress: sdk.ConsAddress(data.ProviderAddr).String(),
			ConsumerAddress: consumerAddr.String(),
			ConsumerKey:     data.ConsumerKey,
		})
	}

	return &types.QueryAllPairsValConAddrByConsumerChainIDResponse{
		PairValConAddr: pairValConAddrs,
	}, nil
}

// QueryParams returns all parameters and current values of provider
func (k Keeper) QueryParams(goCtx context.Context, req *types.QueryParamsRequest) (*types.QueryParamsResponse, error) {
	if req == nil {
		return nil, status.Error(codes.InvalidArgument, "empty request")
	}

	ctx := sdk.UnwrapSDKContext(goCtx)
	params := k.GetParams(ctx)

	return &types.QueryParamsResponse{Params: params}, nil
}

// QueryConsumerChainOptedInValidators returns all validators that opted-in to a given consumer chain
func (k Keeper) QueryConsumerChainOptedInValidators(goCtx context.Context, req *types.QueryConsumerChainOptedInValidatorsRequest) (*types.QueryConsumerChainOptedInValidatorsResponse, error) {
	if req == nil {
		return nil, status.Errorf(codes.InvalidArgument, "empty request")
	} else if req.ChainId != "" {
		return nil, status.Errorf(codes.InvalidArgument, "ChainId has been deprecated. Use ConsumerId instead.")
	}

	consumerId := req.ConsumerId
	if err := types.ValidateConsumerId(consumerId); err != nil {
		return nil, status.Error(codes.InvalidArgument, errorsmod.Wrap(types.ErrInvalidConsumerId, consumerId).Error())
	}

	optedInVals := []string{}
	ctx := sdk.UnwrapSDKContext(goCtx)

	if !k.IsConsumerProposedOrRegistered(ctx, consumerId) {
		return nil, status.Error(codes.InvalidArgument, fmt.Sprintf("unknown consumer chain: %s", consumerId))
	}

	for _, v := range k.GetAllOptedIn(ctx, consumerId) {
		optedInVals = append(optedInVals, v.ToSdkConsAddr().String())
	}

	return &types.QueryConsumerChainOptedInValidatorsResponse{
		ValidatorsProviderAddresses: optedInVals,
	}, nil
}

// QueryConsumerValidators returns all validators that are consumer validators in a given consumer chain
func (k Keeper) QueryConsumerValidators(goCtx context.Context, req *types.QueryConsumerValidatorsRequest) (*types.QueryConsumerValidatorsResponse, error) {
	if req == nil {
		return nil, status.Errorf(codes.InvalidArgument, "empty request")
	} else if req.ChainId != "" {
		return nil, status.Errorf(codes.InvalidArgument, "ChainId has been deprecated. Use ConsumerId instead.")
	}
	consumerId := req.ConsumerId
	if err := types.ValidateConsumerId(consumerId); err != nil {
		return nil, status.Error(codes.InvalidArgument, errorsmod.Wrap(types.ErrInvalidConsumerId, consumerId).Error())
	}

	ctx := sdk.UnwrapSDKContext(goCtx)

	if _, found := k.GetConsumerClientId(ctx, consumerId); !found {
		// chain has to have started; consumer client id is set for a chain during the chain's spawn time
		return nil, status.Error(codes.InvalidArgument, fmt.Sprintf("no started consumer chain: %s", consumerId))
	}

	var validators []*types.QueryConsumerValidatorsValidator

	consumerValSet, err := k.GetConsumerValSet(ctx, consumerId)
	if err != nil {
		return nil, status.Error(codes.Internal, err.Error())
	}

	for _, consumerVal := range consumerValSet {
		provAddr := types.ProviderConsAddress{Address: consumerVal.ProviderConsAddr}
		consAddr := provAddr.ToSdkConsAddr()

		providerVal, err := k.stakingKeeper.GetValidatorByConsAddr(ctx, consAddr)
		if err != nil {
			k.Logger(ctx).Error("cannot find consensus address for provider address:%s", provAddr.String())
			continue
		}

		hasToValidate, err := k.hasToValidate(ctx, provAddr, consumerId)
		if err != nil {
			k.Logger(ctx).Error("cannot define if validator %s has to validate for consumer %s for current epoch",
				provAddr.String(), consumerId)
			continue
		}

		consumerRate, found := k.GetConsumerCommissionRate(ctx, consumerId, types.NewProviderConsAddress(consAddr))
		if !found {
			consumerRate = providerVal.Commission.Rate
		}

		validators = append(validators, &types.QueryConsumerValidatorsValidator{
			ProviderAddress:         sdk.ConsAddress(consumerVal.ProviderConsAddr).String(),
			ConsumerKey:             consumerVal.PublicKey,
			ConsumerPower:           consumerVal.Power,
			ConsumerCommissionRate:  consumerRate,
			Description:             providerVal.Description,
			ProviderOperatorAddress: providerVal.OperatorAddress,
			Jailed:                  providerVal.Jailed,
			Status:                  providerVal.Status,
			ProviderTokens:          providerVal.Tokens,
			ProviderCommissionRate:  providerVal.Commission.Rate,
			ProviderPower:           providerVal.GetConsensusPower(k.stakingKeeper.PowerReduction(ctx)),
			ValidatesCurrentEpoch:   hasToValidate,
		})
	}
	return &types.QueryConsumerValidatorsResponse{
		Validators: validators,
	}, nil
}

// QueryConsumerChainsValidatorHasToValidate returns all consumer chains that the given validator has to validate now
// or in the next epoch if nothing changes.
func (k Keeper) QueryConsumerChainsValidatorHasToValidate(goCtx context.Context, req *types.QueryConsumerChainsValidatorHasToValidateRequest) (*types.QueryConsumerChainsValidatorHasToValidateResponse, error) {
	if req == nil {
		return nil, status.Error(codes.InvalidArgument, "empty request")
	}

	if req.ProviderAddress == "" {
		return nil, status.Error(codes.InvalidArgument, "empty provider address")
	}

	consAddr, err := sdk.ConsAddressFromBech32(req.ProviderAddress)
	if err != nil {
		return nil, status.Error(codes.InvalidArgument, "invalid provider address")
	}

	ctx := sdk.UnwrapSDKContext(goCtx)

	provAddr := types.NewProviderConsAddress(consAddr)

	// get all the consumer chains for which the validator is either already
	// opted-in, currently a consumer validator or if its voting power is within the TopN validators
	consumersToValidate := []string{}
	for _, consumerChainID := range k.GetAllRegisteredConsumerIds(ctx) {
		if hasToValidate, err := k.hasToValidate(ctx, provAddr, consumerChainID); err == nil && hasToValidate {
			consumersToValidate = append(consumersToValidate, consumerChainID)
		}
	}

	return &types.QueryConsumerChainsValidatorHasToValidateResponse{
		ConsumerChainIds: consumersToValidate,
	}, nil
}

// hasToValidate checks if a validator needs to validate on a consumer chain
func (k Keeper) hasToValidate(
	ctx sdk.Context,
	provAddr types.ProviderConsAddress,
	consumerId string,
) (bool, error) {
	// if the validator was sent as part of the packet in the last epoch, it has to validate
	if k.IsConsumerValidator(ctx, consumerId, provAddr) {
		return true, nil
	}

	// if the validator was not part of the last epoch, check if the validator is going to be part of te next epoch
	activeValidators, err := k.GetLastProviderConsensusActiveValidators(ctx)
	if err != nil {
		return false, nil
	}
	if topN := k.GetTopN(ctx, consumerId); topN > 0 {
		// in a Top-N chain, we automatically opt in all validators that belong to the top N
		minPower, found := k.GetMinimumPowerInTopN(ctx, consumerId)
		if found {
			k.OptInTopNValidators(ctx, consumerId, activeValidators, minPower)
		} else {
			k.Logger(ctx).Error("did not find min power in top N for chain", "chain", consumerId)
		}
	}

	// if the validator is opted in and belongs to the validators of the next epoch, then if nothing changes
	// the validator would have to validate in the next epoch
	if k.IsOptedIn(ctx, consumerId, provAddr) {
		lastVals, err := k.GetLastBondedValidators(ctx)
		if err != nil {
			return false, err
		}
		nextValidators := k.ComputeNextValidators(ctx, consumerId, lastVals)
		for _, v := range nextValidators {
			consAddr := sdk.ConsAddress(v.ProviderConsAddr)
			if provAddr.ToSdkConsAddr().Equals(consAddr) {
				return true, nil
			}
		}
	}

	return false, nil
}

// QueryValidatorConsumerCommissionRate returns the commission rate a given
// validator charges on a given consumer chain
func (k Keeper) QueryValidatorConsumerCommissionRate(goCtx context.Context, req *types.QueryValidatorConsumerCommissionRateRequest) (*types.QueryValidatorConsumerCommissionRateResponse, error) {
	if req == nil {
		return nil, status.Errorf(codes.InvalidArgument, "empty request")
	} else if req.ChainId != "" {
		return nil, status.Errorf(codes.InvalidArgument, "ChainId has been deprecated. Use ConsumerId instead.")
	}

	consumerId := req.ConsumerId
	if err := types.ValidateConsumerId(consumerId); err != nil {
		return nil, status.Error(codes.InvalidArgument, errorsmod.Wrap(types.ErrInvalidConsumerId, consumerId).Error())
	}

	consAddr, err := sdk.ConsAddressFromBech32(req.ProviderAddress)
	if err != nil {
		return nil, status.Error(codes.InvalidArgument, "invalid provider address")
	}

	ctx := sdk.UnwrapSDKContext(goCtx)

	if !k.IsConsumerProposedOrRegistered(ctx, consumerId) {
		return nil, status.Error(codes.InvalidArgument, fmt.Sprintf("unknown consumer chain: %s", consumerId))
	}

	res := &types.QueryValidatorConsumerCommissionRateResponse{}

	// Check if the validator has a commission rate set for the consumer chain,
	// otherwise use the commission rate from the validator staking module struct
	consumerRate, found := k.GetConsumerCommissionRate(ctx, consumerId, types.NewProviderConsAddress(consAddr))
	if found {
		res.Rate = consumerRate
	} else {
		v, err := k.stakingKeeper.GetValidatorByConsAddr(ctx, consAddr)
		if err != nil {
			return nil, status.Error(codes.InvalidArgument, fmt.Sprintf("unknown validator: %s", consAddr.String()))
		}
		res.Rate = v.Commission.Rate
	}

	return res, nil
}

// QueryBlocksUntilNextEpoch returns the number of blocks until the next epoch
func (k Keeper) QueryBlocksUntilNextEpoch(goCtx context.Context, req *types.QueryBlocksUntilNextEpochRequest) (*types.QueryBlocksUntilNextEpochResponse, error) {
	ctx := sdk.UnwrapSDKContext(goCtx)

	// Calculate the blocks until the next epoch
	blocksUntilNextEpoch := k.BlocksUntilNextEpoch(ctx)

	return &types.QueryBlocksUntilNextEpochResponse{BlocksUntilNextEpoch: uint64(blocksUntilNextEpoch)}, nil
}

// QueryConsumerIdFromClientId returns the consumer id of the chain associated with this client id
func (k Keeper) QueryConsumerIdFromClientId(goCtx context.Context, req *types.QueryConsumerIdFromClientIdRequest) (*types.QueryConsumerIdFromClientIdResponse, error) {
	ctx := sdk.UnwrapSDKContext(goCtx)

	consumerId, found := k.GetClientIdToConsumerId(ctx, req.ClientId)
	if !found {
		return nil, status.Error(codes.InvalidArgument, fmt.Sprintf("no known consumer chain for this client id: %s", req.ClientId))
	}

	return &types.QueryConsumerIdFromClientIdResponse{ConsumerId: consumerId}, nil
}
