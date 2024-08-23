package keeper

import (
	"context"
	errorsmod "cosmossdk.io/errors"
	"fmt"
	tmtypes "github.com/cometbft/cometbft/types"
	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v5/x/ccv/types"
	"strings"
	"time"
)

type msgServer struct {
	*Keeper
}

// NewMsgServerImpl returns an implementation of the bank MsgServer interface
// for the provided Keeper.
func NewMsgServerImpl(keeper *Keeper) types.MsgServer {
	return &msgServer{Keeper: keeper}
}

var _ types.MsgServer = msgServer{}

// UpdateParams updates the params.
func (k msgServer) UpdateParams(goCtx context.Context, msg *types.MsgUpdateParams) (*types.MsgUpdateParamsResponse, error) {
	if k.GetAuthority() != msg.Authority {
		return nil, errorsmod.Wrapf(govtypes.ErrInvalidSigner, "invalid authority; expected %s, got %s", k.authority, msg.Authority)
	}

	if err := msg.Params.Validate(); err != nil {
		return nil, err
	}

	ctx := sdk.UnwrapSDKContext(goCtx)
	k.Keeper.SetParams(ctx, msg.Params)

	return &types.MsgUpdateParamsResponse{}, nil
}

// AssignConsumerKey defines a method to assign a consensus key on a consumer chain
// for a given validator on the provider
func (k msgServer) AssignConsumerKey(goCtx context.Context, msg *types.MsgAssignConsumerKey) (*types.MsgAssignConsumerKeyResponse, error) {
	ctx := sdk.UnwrapSDKContext(goCtx)

	providerValidatorAddr, err := sdk.ValAddressFromBech32(msg.ProviderAddr)
	if err != nil {
		return nil, err
	}

	// validator must already be registered
	validator, err := k.stakingKeeper.GetValidator(ctx, providerValidatorAddr)
	if err != nil && err == stakingtypes.ErrNoValidatorFound {
		return nil, stakingtypes.ErrNoValidatorFound
	} else if err != nil {
		return nil, err
	}

	consumerTMPublicKey, err := k.ParseConsumerKey(msg.ConsumerKey)
	if err != nil {
		return nil, err
	}

	if err := k.Keeper.AssignConsumerKey(ctx, msg.ConsumerId, validator, consumerTMPublicKey); err != nil {
		return nil, err
	}
	k.Logger(ctx).Info("assigned consumer key",
		"consumer id", msg.ConsumerId,
		"validator operator addr", msg.ProviderAddr,
		"consumer public key", msg.ConsumerKey,
	)

	ctx.EventManager().EmitEvents(sdk.Events{
		sdk.NewEvent(
			types.EventTypeAssignConsumerKey,
			sdk.NewAttribute(types.AttributeProviderValidatorAddress, msg.ProviderAddr),
			sdk.NewAttribute(types.AttributeConsumerConsensusPubKey, msg.ConsumerKey),
		),
	})

	return &types.MsgAssignConsumerKeyResponse{}, nil
}

// RemoveConsumer defines an RPC handler method for MsgRemoveConsumer
func (k msgServer) RemoveConsumer(
	goCtx context.Context,
	msg *types.MsgRemoveConsumer) (*types.MsgRemoveConsumerResponse, error) {
	if k.GetAuthority() != msg.Authority {
		return nil, errorsmod.Wrapf(types.ErrUnauthorized, "expected %s, got %s", k.GetAuthority(), msg.Authority)
	}

	ctx := sdk.UnwrapSDKContext(goCtx)

	consumerId := msg.ConsumerId

	phase, found := k.Keeper.GetConsumerPhase(ctx, consumerId)
	if !found || phase != Launched {
		return nil, errorsmod.Wrapf(types.ErrInvalidPhase,
			"chain with consumer id: %s has to be in its launched phase", consumerId)
	}

	previousStopTime, err := k.Keeper.GetConsumerStopTime(ctx, consumerId)
	if err == nil {
		k.Keeper.RemoveConsumerFromToBeStoppedConsumers(ctx, consumerId, previousStopTime)
	}

	k.Keeper.SetConsumerStopTime(ctx, consumerId, msg.StopTime)
	k.Keeper.AppendStopTimeForConsumerToBeStopped(ctx, consumerId, msg.StopTime)

	return &types.MsgRemoveConsumerResponse{}, nil
}

// ChangeRewardDenoms defines a rpc handler method for MsgChangeRewardDenoms
func (k msgServer) ChangeRewardDenoms(goCtx context.Context, msg *types.MsgChangeRewardDenoms) (*types.MsgChangeRewardDenomsResponse, error) {
	if k.GetAuthority() != msg.Authority {
		return nil, errorsmod.Wrapf(types.ErrUnauthorized, "expected %s, got %s", k.GetAuthority(), msg.Authority)
	}

	sdkCtx := sdk.UnwrapSDKContext(goCtx)
	err := k.Keeper.HandleConsumerRewardDenomProposal(sdkCtx, msg)
	if err != nil {
		return nil, errorsmod.Wrapf(err, "failed handling Change Reward Denoms proposal")
	}

	return &types.MsgChangeRewardDenomsResponse{}, nil
}

func (k msgServer) SubmitConsumerMisbehaviour(goCtx context.Context, msg *types.MsgSubmitConsumerMisbehaviour) (*types.MsgSubmitConsumerMisbehaviourResponse, error) {
	ctx := sdk.UnwrapSDKContext(goCtx)
	if err := k.Keeper.HandleConsumerMisbehaviour(ctx, msg.ConsumerId, *msg.Misbehaviour); err != nil {
		return nil, err
	}

	ctx.EventManager().EmitEvents(sdk.Events{
		sdk.NewEvent(
			ccvtypes.EventTypeSubmitConsumerMisbehaviour,
			sdk.NewAttribute(ccvtypes.AttributeConsumerMisbehaviour, msg.Misbehaviour.String()),
			sdk.NewAttribute(ccvtypes.AttributeSubmitterAddress, msg.Submitter),
			sdk.NewAttribute(ccvtypes.AttributeMisbehaviourClientId, msg.Misbehaviour.ClientId),
			sdk.NewAttribute(ccvtypes.AttributeMisbehaviourHeight1, msg.Misbehaviour.Header1.GetHeight().String()),
			sdk.NewAttribute(ccvtypes.AttributeMisbehaviourHeight2, msg.Misbehaviour.Header2.GetHeight().String()),
		),
	})

	return &types.MsgSubmitConsumerMisbehaviourResponse{}, nil
}

func (k msgServer) SubmitConsumerDoubleVoting(goCtx context.Context, msg *types.MsgSubmitConsumerDoubleVoting) (*types.MsgSubmitConsumerDoubleVotingResponse, error) {
	ctx := sdk.UnwrapSDKContext(goCtx)

	evidence, err := tmtypes.DuplicateVoteEvidenceFromProto(msg.DuplicateVoteEvidence)
	if err != nil {
		return nil, err
	}

	// parse the validator set of the infraction block header in order
	// to find the public key of the validator who double voted

	// get validator set
	valset, err := tmtypes.ValidatorSetFromProto(msg.InfractionBlockHeader.ValidatorSet)
	if err != nil {
		return nil, err
	}

	// look for the malicious validator in the validator set
	_, validator := valset.GetByAddress(evidence.VoteA.ValidatorAddress)
	if validator == nil {
		return nil, errorsmod.Wrapf(
			ccvtypes.ErrInvalidDoubleVotingEvidence,
			"misbehaving validator %s cannot be found in the infraction block header validator set",
			evidence.VoteA.ValidatorAddress)
	}

	pubkey, err := cryptocodec.FromTmPubKeyInterface(validator.PubKey)
	if err != nil {
		return nil, err
	}

	// handle the double voting evidence using the malicious validator's public key
	consumerId := msg.ConsumerId
	if err := k.Keeper.HandleConsumerDoubleVoting(ctx, consumerId, evidence, pubkey); err != nil {
		return nil, err
	}

	ctx.EventManager().EmitEvents(sdk.Events{
		sdk.NewEvent(
			ccvtypes.EventTypeSubmitConsumerDoubleVoting,
			sdk.NewAttribute(ccvtypes.AttributeConsumerDoubleVoting, msg.DuplicateVoteEvidence.String()),
			sdk.NewAttribute(ccvtypes.AttributeChainID, msg.InfractionBlockHeader.Header.ChainID),
			sdk.NewAttribute(ccvtypes.AttributeSubmitterAddress, msg.Submitter),
		),
	})

	return &types.MsgSubmitConsumerDoubleVotingResponse{}, nil
}

func (k msgServer) OptIn(goCtx context.Context, msg *types.MsgOptIn) (*types.MsgOptInResponse, error) {
	ctx := sdk.UnwrapSDKContext(goCtx)

	valAddress, err := sdk.ValAddressFromBech32(msg.ProviderAddr)
	if err != nil {
		return nil, err
	}

	// validator must already be registered
	validator, err := k.stakingKeeper.GetValidator(ctx, valAddress)
	if err != nil {
		return nil, err
	}

	consAddrTmp, err := validator.GetConsAddr()
	if err != nil {
		return nil, err
	}
	providerConsAddr := types.NewProviderConsAddress(consAddrTmp)

	err = k.Keeper.HandleOptIn(ctx, msg.ConsumerId, providerConsAddr, msg.ConsumerKey)
	if err != nil {
		return nil, err
	}

	ctx.EventManager().EmitEvents(sdk.Events{
		sdk.NewEvent(
			types.EventTypeOptIn,
			sdk.NewAttribute(types.AttributeProviderValidatorAddress, msg.ProviderAddr),
			sdk.NewAttribute(types.AttributeConsumerConsensusPubKey, msg.ConsumerKey),
		),
	})

	return &types.MsgOptInResponse{}, nil
}

func (k msgServer) OptOut(goCtx context.Context, msg *types.MsgOptOut) (*types.MsgOptOutResponse, error) {
	ctx := sdk.UnwrapSDKContext(goCtx)

	valAddress, err := sdk.ValAddressFromBech32(msg.ProviderAddr)
	if err != nil {
		return nil, err
	}

	// validator must already be registered
	validator, err := k.stakingKeeper.GetValidator(ctx, valAddress)
	if err != nil {
		return nil, err
	}

	consAddrTmp, err := validator.GetConsAddr()
	if err != nil {
		return nil, err
	}
	providerConsAddr := types.NewProviderConsAddress(consAddrTmp)

	err = k.Keeper.HandleOptOut(ctx, msg.ConsumerId, providerConsAddr)
	if err != nil {
		return nil, err
	}

	ctx.EventManager().EmitEvents(sdk.Events{
		sdk.NewEvent(
			types.EventTypeOptOut,
			sdk.NewAttribute(types.AttributeProviderValidatorAddress, msg.ProviderAddr),
		),
	})

	return &types.MsgOptOutResponse{}, nil
}

func (k msgServer) SetConsumerCommissionRate(goCtx context.Context, msg *types.MsgSetConsumerCommissionRate) (*types.MsgSetConsumerCommissionRateResponse, error) {
	ctx := sdk.UnwrapSDKContext(goCtx)

	providerValidatorAddr, err := sdk.ValAddressFromBech32(msg.ProviderAddr)
	if err != nil {
		return nil, err
	}

	// validator must already be registered
	validator, err := k.stakingKeeper.GetValidator(ctx, providerValidatorAddr)
	if err != nil {
		return nil, stakingtypes.ErrNoValidatorFound
	}

	consAddr, err := validator.GetConsAddr()
	if err != nil {
		return nil, err
	}

	if err := k.HandleSetConsumerCommissionRate(ctx, msg.ConsumerId, types.NewProviderConsAddress(consAddr), msg.Rate); err != nil {
		return nil, err
	}

	ctx.EventManager().EmitEvents(sdk.Events{
		sdk.NewEvent(
			types.EventTypeSetConsumerCommissionRate,
			sdk.NewAttribute(types.AttributeConsumerId, msg.ConsumerId),
			sdk.NewAttribute(types.AttributeProviderValidatorAddress, msg.ProviderAddr),
			sdk.NewAttribute(types.AttributeConsumerCommissionRate, msg.Rate.String()),
		),
	})

	return &types.MsgSetConsumerCommissionRateResponse{}, nil
}

// CreateConsumer creates a consumer chain
func (k msgServer) CreateConsumer(goCtx context.Context, msg *types.MsgCreateConsumer) (*types.MsgCreateConsumerResponse, error) {
	ctx := sdk.UnwrapSDKContext(goCtx)

	consumerId := k.FetchAndIncrementConsumerId(ctx)

	k.SetConsumerOwnerAddress(ctx, consumerId, msg.Signer)
	k.SetConsumerChainId(ctx, consumerId, msg.ChainId)
	k.SetConsumerPhase(ctx, consumerId, Registered)

	if err := k.SetConsumerMetadata(ctx, consumerId, msg.Metadata); err != nil {
		return &types.MsgCreateConsumerResponse{}, errorsmod.Wrapf(types.ErrInvalidConsumerMetadata,
			"cannot set consumer metadata: %s", err.Error())
	}

	// initialization parameters are optional and hence could be nil
	if msg.InitializationParameters != nil {
		if err := k.SetConsumerInitializationParameters(ctx, consumerId, *msg.InitializationParameters); err != nil {
			return &types.MsgCreateConsumerResponse{}, errorsmod.Wrapf(types.ErrInvalidConsumerInitializationParameters,
				"cannot set consumer initialization parameters: %s", err.Error())
		}
	}

	// power-shaping parameters are optional and hence could be null
	if msg.PowerShapingParameters != nil {
		if msg.PowerShapingParameters.Top_N != 0 {
			return &types.MsgCreateConsumerResponse{}, errorsmod.Wrap(types.ErrCannotCreateTopNChain,
				"cannot create a Top N chain using the `MsgCreateConsumer` message; use `MsgUpdateConsumer` instead")
		}
		if err := k.SetConsumerPowerShapingParameters(ctx, consumerId, *msg.PowerShapingParameters); err != nil {
			return &types.MsgCreateConsumerResponse{}, errorsmod.Wrapf(types.ErrInvalidPowerShapingParameters,
				"cannot set power shaping parameters")
		}
	}

	if spawnTime, canLaunch := k.CanLaunch(ctx, consumerId); canLaunch {
		k.SetConsumerPhase(ctx, consumerId, Initialized)
		k.PrepareConsumerForLaunch(ctx, consumerId, time.Time{}, spawnTime)
	}

	return &types.MsgCreateConsumerResponse{ConsumerId: consumerId}, nil
}

// UpdateConsumer updates the record of a consumer chain
func (k msgServer) UpdateConsumer(goCtx context.Context, msg *types.MsgUpdateConsumer) (*types.MsgUpdateConsumerResponse, error) {
	ctx := sdk.UnwrapSDKContext(goCtx)
	consumerId := msg.ConsumerId

	phase, found := k.GetConsumerPhase(ctx, consumerId)
	if found && phase == Stopped {
		return &types.MsgUpdateConsumerResponse{}, errorsmod.Wrapf(types.ErrInvalidPhase,
			"cannot update consumer chain that is in the stopped phase: %s", consumerId)
	}

	ownerAddress, err := k.Keeper.GetConsumerOwnerAddress(ctx, consumerId)
	if err != nil {
		return &types.MsgUpdateConsumerResponse{}, errorsmod.Wrapf(types.ErrNoOwnerAddress, "cannot retrieve owner address %s", ownerAddress)
	}

	if msg.Signer != ownerAddress {
		return &types.MsgUpdateConsumerResponse{}, errorsmod.Wrapf(types.ErrUnauthorized, "expected owner address %s, got %s", ownerAddress, msg.Signer)
	}

	if strings.TrimSpace(msg.NewOwnerAddress) != "" {
		k.Keeper.SetConsumerOwnerAddress(ctx, consumerId, msg.NewOwnerAddress)
	}

	if msg.Metadata != nil {
		if err := k.SetConsumerMetadata(ctx, consumerId, *msg.Metadata); err != nil {
			return &types.MsgUpdateConsumerResponse{}, errorsmod.Wrapf(types.ErrInvalidConsumerMetadata,
				"cannot set consumer metadata: %s", err.Error())
		}
	}

	// get the previous spawn time so that we can use it in `PrepareConsumerForLaunch`
	var previousSpawnTime time.Time
	if previousInitializationParameters, err := k.Keeper.GetConsumerInitializationParameters(ctx, msg.ConsumerId); err != nil {
		previousSpawnTime = previousInitializationParameters.SpawnTime
	}

	if msg.InitializationParameters != nil {
		if err = k.Keeper.SetConsumerInitializationParameters(ctx, msg.ConsumerId, *msg.InitializationParameters); err != nil {
			return &types.MsgUpdateConsumerResponse{}, errorsmod.Wrapf(types.ErrInvalidConsumerInitializationParameters,
				"cannot set consumer initialization parameters: %s", err.Error())
		}
	}

	if msg.PowerShapingParameters != nil {
		// A consumer chain can only become a Top N chain if the owner is the gov module. Because of this, to create a
		// Top N chain, we need two `MsgUpdateConsumer` messages: i) one that would set the `ownerAddress` to the gov module
		// and ii) one that would set the `Top_N` to something greater than 0.
		if msg.PowerShapingParameters.Top_N > 0 && ownerAddress != k.GetAuthority() {
			return &types.MsgUpdateConsumerResponse{}, errorsmod.Wrapf(types.ErrInvalidTransformToTopN,
				"an update to a Top N chain can only be done if chain is owner is the gov module")
		}

		oldTopN := k.Keeper.GetTopN(ctx, consumerId)
		if err = k.SetConsumerPowerShapingParameters(ctx, consumerId, *msg.PowerShapingParameters); err != nil {
			return &types.MsgUpdateConsumerResponse{}, errorsmod.Wrapf(types.ErrInvalidPowerShapingParameters,
				"cannot set power shaping parameters")
		}

		k.Keeper.UpdateAllowlist(ctx, consumerId, msg.PowerShapingParameters.Allowlist)
		k.Keeper.UpdateDenylist(ctx, consumerId, msg.PowerShapingParameters.Denylist)
		err = k.Keeper.UpdateMinimumPowerInTopN(ctx, consumerId, oldTopN, msg.PowerShapingParameters.Top_N)
		if err != nil {
			return &types.MsgUpdateConsumerResponse{}, errorsmod.Wrapf(types.ErrCannotUpdateMinimumPowerInTopN,
				"could not update minimum power in top N, oldTopN: %d, newTopN: %d, error: %s", oldTopN, msg.PowerShapingParameters.Top_N, err.Error())
		}
	}

	// A Top N cannot change its owner address to something different from the gov module if the chain
	// remains a Top N chain.
	currentOwnerAddress, err := k.GetConsumerOwnerAddress(ctx, consumerId)
	if err != nil {
		return &types.MsgUpdateConsumerResponse{}, errorsmod.Wrapf(types.ErrNoOwnerAddress, "cannot retrieve owner address %s: %s", ownerAddress, err.Error())
	}

	currentPowerShapingParameters, err := k.GetConsumerPowerShapingParameters(ctx, consumerId)
	if err != nil {
		return &types.MsgUpdateConsumerResponse{}, errorsmod.Wrapf(types.ErrInvalidPowerShapingParameters, "cannot retrieve power shaping parameters: %s", err.Error())
	}

	if currentPowerShapingParameters.Top_N != 0 && currentOwnerAddress != k.GetAuthority() {
		return &types.MsgUpdateConsumerResponse{}, errorsmod.Wrapf(types.ErrInvalidTransformToOptIn,
			"a move to a new owner address that is not the gov module can only be done if `Top N` is set to 0")
	}

	if spawnTime, canLaunch := k.CanLaunch(ctx, consumerId); canLaunch {
		k.SetConsumerPhase(ctx, consumerId, Initialized)
		k.PrepareConsumerForLaunch(ctx, consumerId, previousSpawnTime, spawnTime)
	}

	return &types.MsgUpdateConsumerResponse{}, nil
}

func (k msgServer) ConsumerAddition(_ context.Context, _ *types.MsgConsumerAddition) (*types.MsgConsumerAdditionResponse, error) {
	return nil, fmt.Errorf("`MsgConsumerAddition` is deprecated. Use `MsgCreateConsumer`")
}

func (k msgServer) ConsumerModification(_ context.Context, _ *types.MsgConsumerModification) (*types.MsgConsumerModificationResponse, error) {
	return nil, fmt.Errorf("`MsgConsumerModification` is deprecated. Use `MsgUpdateConsumer` instead")
}

func (k msgServer) ConsumerRemoval(_ context.Context, _ *types.MsgConsumerRemoval) (*types.MsgConsumerRemovalResponse, error) {
	return nil, fmt.Errorf("`MsgConsumerRemoval` is deprecated. Use `MsgRemoveConsumer` instead")
}
