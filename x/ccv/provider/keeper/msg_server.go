package keeper

import (
	"context"
	"fmt"
	"strings"
	"time"

	errorsmod "cosmossdk.io/errors"
	tmtypes "github.com/cometbft/cometbft/types"
	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v5/x/ccv/types"
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

// ChangeRewardDenoms defines a rpc handler method for MsgChangeRewardDenoms
func (k msgServer) ChangeRewardDenoms(goCtx context.Context, msg *types.MsgChangeRewardDenoms) (*types.MsgChangeRewardDenomsResponse, error) {
	ctx := sdk.UnwrapSDKContext(goCtx)

	if k.GetAuthority() != msg.Authority {
		return nil, errorsmod.Wrapf(types.ErrUnauthorized, "expected %s, got %s", k.GetAuthority(), msg.Authority)
	}

	eventAttributes := k.Keeper.ChangeRewardDenoms(ctx, msg.DenomsToAdd, msg.DenomsToRemove)

	ctx.EventManager().EmitEvent(
		sdk.NewEvent(
			types.EventTypeChangeConsumerRewardDenom,
			eventAttributes...,
		),
	)

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
			sdk.NewAttribute(types.AttributeSubmitterAddress, msg.Submitter),
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
			sdk.NewAttribute(types.AttributeConsumerID, msg.ConsumerId),
			sdk.NewAttribute(types.AttributeConsumerChainID, msg.InfractionBlockHeader.Header.ChainID),
			sdk.NewAttribute(types.AttributeSubmitterAddress, msg.Submitter),
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
			sdk.NewAttribute(types.AttributeConsumerID, msg.ConsumerId),
			sdk.NewAttribute(types.AttributeProviderValidatorAddress, msg.ProviderAddr),
			sdk.NewAttribute(types.AttributeConsumerCommissionRate, msg.Rate.String()),
		),
	})

	return &types.MsgSetConsumerCommissionRateResponse{}, nil
}

// CreateConsumer creates a consumer chain
func (k msgServer) CreateConsumer(goCtx context.Context, msg *types.MsgCreateConsumer) (*types.MsgCreateConsumerResponse, error) {
	ctx := sdk.UnwrapSDKContext(goCtx)
	resp := types.MsgCreateConsumerResponse{}

	// initialize an empty slice to store event attributes
	eventAttributes := []sdk.Attribute{}

	consumerId := k.Keeper.FetchAndIncrementConsumerId(ctx)

	k.Keeper.SetConsumerOwnerAddress(ctx, consumerId, msg.Submitter)
	k.Keeper.SetConsumerChainId(ctx, consumerId, msg.ChainId)
	k.Keeper.SetConsumerPhase(ctx, consumerId, types.CONSUMER_PHASE_REGISTERED)

	if err := k.Keeper.SetConsumerMetadata(ctx, consumerId, msg.Metadata); err != nil {
		return &resp, errorsmod.Wrapf(types.ErrInvalidConsumerMetadata,
			"cannot set consumer metadata: %s", err.Error())
	}

	// add event attributes
	eventAttributes = append(eventAttributes, []sdk.Attribute{
		sdk.NewAttribute(sdk.AttributeKeyModule, types.ModuleName),
		sdk.NewAttribute(types.AttributeConsumerID, consumerId),
		sdk.NewAttribute(types.AttributeConsumerChainID, msg.ChainId),
		sdk.NewAttribute(types.AttributeConsumerName, msg.Metadata.Name),
		sdk.NewAttribute(types.AttributeSubmitterAddress, msg.Submitter),
		sdk.NewAttribute(types.AttributeConsumerOwner, msg.Submitter),
	}...)

	// initialization parameters are optional and hence could be nil;
	// in that case, set the default
	initializationParameters := types.ConsumerInitializationParameters{} // default params
	if msg.InitializationParameters != nil {
		initializationParameters = *msg.InitializationParameters
	}
	if err := k.Keeper.SetConsumerInitializationParameters(ctx, consumerId, initializationParameters); err != nil {
		return &resp, errorsmod.Wrapf(types.ErrInvalidConsumerInitializationParameters,
			"cannot set consumer initialization parameters: %s", err.Error())
	}
	if !initializationParameters.SpawnTime.IsZero() {
		// add SpawnTime event attribute
		eventAttributes = append(eventAttributes,
			sdk.NewAttribute(types.AttributeConsumerSpawnTime, initializationParameters.SpawnTime.String()))
	}

	// power-shaping parameters are optional and hence could be nil;
	// in that case, set the default
	powerShapingParameters := types.PowerShapingParameters{} // default params
	if msg.PowerShapingParameters != nil {
		powerShapingParameters = *msg.PowerShapingParameters

		if powerShapingParameters.Top_N != 0 {
			return &resp, errorsmod.Wrap(types.ErrCannotCreateTopNChain,
				"cannot create a Top N chain using the `MsgCreateConsumer` message; use `MsgUpdateConsumer` instead")
		}
	}
	if err := k.Keeper.SetConsumerPowerShapingParameters(ctx, consumerId, powerShapingParameters); err != nil {
		return &resp, errorsmod.Wrapf(types.ErrInvalidPowerShapingParameters,
			"cannot set power shaping parameters")
	}

	if spawnTime, canLaunch := k.Keeper.CanLaunch(ctx, consumerId); canLaunch {
		k.Keeper.SetConsumerPhase(ctx, consumerId, types.CONSUMER_PHASE_INITIALIZED)
		if err := k.Keeper.PrepareConsumerForLaunch(ctx, consumerId, time.Time{}, spawnTime); err != nil {
			return &resp, errorsmod.Wrapf(types.ErrCannotPrepareForLaunch,
				"cannot prepare chain with consumer id (%s) for launch", consumerId)
		}
	}

	// add Phase event attribute
	eventAttributes = append(eventAttributes,
		sdk.NewAttribute(types.AttributeConsumerSpawnTime, k.GetConsumerPhase(ctx, consumerId).String()))

	ctx.EventManager().EmitEvent(
		sdk.NewEvent(
			types.EventTypeCreateConsumer,
			eventAttributes...,
		),
	)

	resp.ConsumerId = consumerId
	return &resp, nil
}

// UpdateConsumer updates the metadata, power-shaping or initialization parameters of a consumer chain
func (k msgServer) UpdateConsumer(goCtx context.Context, msg *types.MsgUpdateConsumer) (*types.MsgUpdateConsumerResponse, error) {
	ctx := sdk.UnwrapSDKContext(goCtx)
	resp := types.MsgUpdateConsumerResponse{}

	// initialize an empty slice to store event attributes
	eventAttributes := []sdk.Attribute{}

	consumerId := msg.ConsumerId

	if !k.Keeper.IsConsumerActive(ctx, consumerId) {
		return &resp, errorsmod.Wrapf(types.ErrInvalidPhase,
			"cannot update consumer chain that is not in the registered, initialized, or launched phase: %s", consumerId)
	}

	ownerAddress, err := k.Keeper.GetConsumerOwnerAddress(ctx, consumerId)
	if err != nil {
		return &resp, errorsmod.Wrapf(types.ErrNoOwnerAddress, "cannot retrieve owner address %s", ownerAddress)
	}

	if msg.Owner != ownerAddress {
		return &resp, errorsmod.Wrapf(types.ErrUnauthorized, "expected owner address %s, got %s", ownerAddress, msg.Owner)
	}

	chainId, err := k.GetConsumerChainId(ctx, consumerId)
	if err != nil {
		return &resp, errorsmod.Wrapf(ccvtypes.ErrInvalidConsumerState,
			"cannot get consumer chain ID: %s", err.Error())
	}

	// add event attributes
	eventAttributes = append(eventAttributes, []sdk.Attribute{
		sdk.NewAttribute(sdk.AttributeKeyModule, types.ModuleName),
		sdk.NewAttribute(types.AttributeConsumerID, consumerId),
		sdk.NewAttribute(types.AttributeConsumerChainID, chainId),
		sdk.NewAttribute(types.AttributeSubmitterAddress, msg.Owner),
	}...)

	// The new owner address can be empty, in which case the consumer chain does not change its owner.
	// However, if the new owner address is not empty, we verify that it's a valid account address.
	if strings.TrimSpace(msg.NewOwnerAddress) != "" {
		if _, err := k.accountKeeper.AddressCodec().StringToBytes(msg.NewOwnerAddress); err != nil {
			return &resp, errorsmod.Wrapf(types.ErrInvalidNewOwnerAddress, "invalid new owner address %s", msg.NewOwnerAddress)
		}

		k.Keeper.SetConsumerOwnerAddress(ctx, consumerId, msg.NewOwnerAddress)

		// add Owner event attribute
		eventAttributes = append(eventAttributes,
			sdk.NewAttribute(types.AttributeConsumerOwner, msg.NewOwnerAddress))
	}

	if msg.Metadata != nil {
		if err := k.Keeper.SetConsumerMetadata(ctx, consumerId, *msg.Metadata); err != nil {
			return &resp, errorsmod.Wrapf(types.ErrInvalidConsumerMetadata,
				"cannot set consumer metadata: %s", err.Error())
		}

		// add Name event attribute
		eventAttributes = append(eventAttributes, sdk.NewAttribute(types.AttributeConsumerName, msg.Metadata.Name))
	}

	// get the previous spawn time so that we can use it in `PrepareConsumerForLaunch`
	previousInitializationParameters, err := k.Keeper.GetConsumerInitializationParameters(ctx, consumerId)
	if err != nil {
		return &resp, errorsmod.Wrapf(ccvtypes.ErrInvalidConsumerState,
			"cannot get consumer initialized parameters, consumerId(%s): %s", consumerId, err.Error())
	}
	previousSpawnTime := previousInitializationParameters.SpawnTime

	if msg.InitializationParameters != nil {
		if err = k.Keeper.SetConsumerInitializationParameters(ctx, msg.ConsumerId, *msg.InitializationParameters); err != nil {
			return &resp, errorsmod.Wrapf(types.ErrInvalidConsumerInitializationParameters,
				"cannot set consumer initialization parameters: %s", err.Error())
		}

		if !msg.InitializationParameters.SpawnTime.IsZero() {
			// add SpawnTime event attribute
			eventAttributes = append(eventAttributes,
				sdk.NewAttribute(types.AttributeConsumerSpawnTime, msg.InitializationParameters.SpawnTime.String()))
		}
	}

	if msg.PowerShapingParameters != nil {
		// A consumer chain can only become a Top N chain if the owner is the gov module. Because of this, to create a
		// Top N chain, we need two `MsgUpdateConsumer` messages: i) one that would set the `ownerAddress` to the gov module
		// and ii) one that would set the `Top_N` to something greater than 0.
		if msg.PowerShapingParameters.Top_N > 0 && ownerAddress != k.GetAuthority() {
			return &resp, errorsmod.Wrapf(types.ErrInvalidTransformToTopN,
				"an update to a Top N chain can only be done if chain is owner is the gov module")
		}

		oldPowerShapingParameters, err := k.Keeper.GetConsumerPowerShapingParameters(ctx, consumerId)
		if err != nil {
			return &resp, errorsmod.Wrapf(ccvtypes.ErrInvalidConsumerState,
				"cannot get consumer previous power shaping parameters: %s", err.Error())
		}
		oldTopN := oldPowerShapingParameters.Top_N

		if err = k.Keeper.SetConsumerPowerShapingParameters(ctx, consumerId, *msg.PowerShapingParameters); err != nil {
			return &resp, errorsmod.Wrapf(types.ErrInvalidPowerShapingParameters,
				"cannot set power shaping parameters")
		}
		err = k.Keeper.UpdateMinimumPowerInTopN(ctx, consumerId, oldTopN, msg.PowerShapingParameters.Top_N)
		if err != nil {
			return &resp, errorsmod.Wrapf(types.ErrCannotUpdateMinimumPowerInTopN,
				"could not update minimum power in top N, oldTopN: %d, newTopN: %d, error: %s", oldTopN, msg.PowerShapingParameters.Top_N, err.Error())
		}

		// add TopN event attribute
		eventAttributes = append(eventAttributes,
			sdk.NewAttribute(types.AttributeConsumerTopN, fmt.Sprintf("%v", msg.PowerShapingParameters.Top_N)))
	}

	// A Top N cannot change its owner address to something different from the gov module if the chain
	// remains a Top N chain.
	currentOwnerAddress, err := k.Keeper.GetConsumerOwnerAddress(ctx, consumerId)
	if err != nil {
		return &resp, errorsmod.Wrapf(ccvtypes.ErrInvalidConsumerState, "cannot retrieve owner address %s: %s", ownerAddress, err.Error())
	}

	currentPowerShapingParameters, err := k.Keeper.GetConsumerPowerShapingParameters(ctx, consumerId)
	if err != nil {
		return &resp, errorsmod.Wrapf(ccvtypes.ErrInvalidConsumerState, "cannot retrieve power shaping parameters: %s", err.Error())
	}

	if currentPowerShapingParameters.Top_N != 0 && currentOwnerAddress != k.GetAuthority() {
		return &resp, errorsmod.Wrapf(types.ErrInvalidTransformToOptIn,
			"a move to a new owner address that is not the gov module can only be done if `Top N` is set to 0")
	}

	if spawnTime, canLaunch := k.Keeper.CanLaunch(ctx, consumerId); canLaunch {
		k.Keeper.SetConsumerPhase(ctx, consumerId, types.CONSUMER_PHASE_INITIALIZED)
		if err := k.Keeper.PrepareConsumerForLaunch(ctx, consumerId, previousSpawnTime, spawnTime); err != nil {
			return &resp, errorsmod.Wrapf(types.ErrCannotPrepareForLaunch,
				"cannot prepare chain with consumer id (%s) for launch", consumerId)
		}
	}

	// add Phase event attribute
	eventAttributes = append(eventAttributes,
		sdk.NewAttribute(types.AttributeConsumerSpawnTime, k.GetConsumerPhase(ctx, consumerId).String()))

	ctx.EventManager().EmitEvent(
		sdk.NewEvent(
			types.EventTypeUpdateConsumer,
			eventAttributes...,
		),
	)

	return &resp, nil
}

// RemoveConsumer defines an RPC handler method for MsgRemoveConsumer
func (k msgServer) RemoveConsumer(goCtx context.Context, msg *types.MsgRemoveConsumer) (*types.MsgRemoveConsumerResponse, error) {
	ctx := sdk.UnwrapSDKContext(goCtx)

	resp := types.MsgRemoveConsumerResponse{}

	consumerId := msg.ConsumerId
	ownerAddress, err := k.Keeper.GetConsumerOwnerAddress(ctx, consumerId)
	if err != nil {
		return &resp, errorsmod.Wrapf(types.ErrNoOwnerAddress, "cannot retrieve owner address %s", ownerAddress)
	}

	if msg.Owner != ownerAddress {
		return &resp, errorsmod.Wrapf(types.ErrUnauthorized, "expected owner address %s, got %s", ownerAddress, msg.Owner)
	}

	phase := k.Keeper.GetConsumerPhase(ctx, consumerId)
	if phase != types.CONSUMER_PHASE_LAUNCHED {
		return &resp, errorsmod.Wrapf(types.ErrInvalidPhase,
			"chain with consumer id: %s has to be in its launched phase", consumerId)
	}

	err = k.Keeper.StopAndPrepareForConsumerRemoval(ctx, consumerId)
	return &resp, err
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
