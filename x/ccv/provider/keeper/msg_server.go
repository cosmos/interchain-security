package keeper

import (
	"context"

	errorsmod "cosmossdk.io/errors"
	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	tmtypes "github.com/cometbft/cometbft/types"

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

func (k msgServer) CreateOptInConsumer(goCtx context.Context, msg *types.MsgCreateConsumer) (*types.MsgCreateConsumerResponse, error) {
	res, err := k.RegisterConsumer(goCtx, msg.MsgRegisterConsumer)
	if err != nil {
		return &types.MsgCreateConsumerResponse{}, err
	}

	// Overwrite with correct ConsumerId
	msgInitialize := &types.MsgInitializeConsumer{
		ConsumerId:           res.ConsumerId,
		Authority:            msg.MsgInitializeConsumer.Authority,
		InitializationRecord: msg.MsgInitializeConsumer.InitializationRecord,
	}
	_, err = k.InitializeConsumer(goCtx, msgInitialize)
	if err != nil {
		return &types.MsgCreateConsumerResponse{}, err
	}

	// Overwrite with correct ConsumerId
	msgUpdate := &types.MsgUpdateConsumer{
		ConsumerId:   res.ConsumerId,
		Authority:    msg.MsgUpdateConsumer.Authority,
		UpdateRecord: msg.MsgUpdateConsumer.UpdateRecord,
	}
	_, err = k.UpdateConsumer(goCtx, msgUpdate)
	if err != nil {
		return &types.MsgCreateConsumerResponse{}, err
	}

	return &types.MsgCreateConsumerResponse{}, nil
}

// RegisterConsumer registers a consumer chain
func (k msgServer) RegisterConsumer(goCtx context.Context, msg *types.MsgRegisterConsumer) (*types.MsgRegisterConsumerResponse, error) {
	ctx := sdk.UnwrapSDKContext(goCtx)

	consumerId := k.Keeper.FetchAndIncrementConsumerId(ctx)

	err := k.Keeper.SetConsumerRegistrationRecord(ctx, consumerId, *msg.RegistrationRecord)
	if err != nil {
		return &types.MsgRegisterConsumerResponse{}, err
	}
	k.Keeper.SetConsumerOwnerAddress(ctx, consumerId, msg.Signer)
	k.Keeper.SetConsumerPhase(ctx, consumerId, Registered)

	return &types.MsgRegisterConsumerResponse{ConsumerId: consumerId}, nil
}

// InitializeConsumer initializes a consumer chain
func (k msgServer) InitializeConsumer(goCtx context.Context, msg *types.MsgInitializeConsumer) (*types.MsgInitializeConsumerResponse, error) {
	ctx := sdk.UnwrapSDKContext(goCtx)

	initGas := ctx.GasMeter().GasConsumed()

	consumerId := msg.ConsumerId

	phase, found := k.Keeper.GetConsumerPhase(ctx, consumerId)
	if !found || (phase != Registered && phase != Initialized) {
		return nil, errorsmod.Wrapf(types.ErrInvalidPhase,
			"chain with consumer id: %s has to be in its registered or initialized phase", consumerId)
	}

	ownerAddress := k.Keeper.GetConsumerOwnerAddress(ctx, consumerId)
	if k.GetAuthority() == msg.Authority {
		// message is executed as part of governance proposal and hence we change the owner address
		// to be the one of the module account address
		k.Keeper.SetConsumerOwnerAddress(ctx, consumerId, k.GetAuthority())
	} else if msg.Authority != ownerAddress {
		return nil, errorsmod.Wrapf(types.ErrUnauthorized, "expected owner address %s, got %s", ownerAddress, msg.Authority)
	}

	// if this is not the first initialization, remove the consumer id from the old spawn time
	record, err := k.Keeper.GetConsumerInitializationRecord(ctx, consumerId)
	if err == nil {
		previousSpawnTime := record.SpawnTime
		k.Keeper.RemoveConsumerFromToBeLaunchedConsumers(ctx, consumerId, previousSpawnTime)
	}

	k.Keeper.SetConsumerInitializationRecord(ctx, consumerId, *msg.InitializationRecord)
	k.Keeper.SetConsumerPhase(ctx, consumerId, Initialized)

	k.Keeper.AppendSpawnTimeForConsumerToBeLaunched(ctx, consumerId, msg.InitializationRecord.SpawnTime)

	gasAfter := ctx.GasMeter().GasConsumed()
	ctx.GasMeter().ConsumeGas(gasAfter-initGas, "initializing a chain has an additional cost during spawn time, "+
		"so charging double the gas here")

	return &types.MsgInitializeConsumerResponse{}, nil
}

// UpdateConsumer updates the record of a consumer chain
func (k msgServer) UpdateConsumer(goCtx context.Context, msg *types.MsgUpdateConsumer) (*types.MsgUpdateConsumerResponse, error) {
	ctx := sdk.UnwrapSDKContext(goCtx)
	consumerId := msg.ConsumerId

	ownerAddress := k.Keeper.GetConsumerOwnerAddress(ctx, consumerId)
	if k.GetAuthority() == msg.Authority {
		// message is executed as part of governance proposal and hence we change the owner address
		// to be the one of the module account address (e.g., a gov proposal with a single `MsgUpdateConsumer` might have
		// led to this)
		k.Keeper.SetConsumerOwnerAddress(ctx, consumerId, k.GetAuthority())
	} else if msg.Authority != ownerAddress {
		return nil, errorsmod.Wrapf(types.ErrUnauthorized, "expected owner address %s, got %s", ownerAddress, msg.Authority)
	}

	k.Keeper.SetConsumerUpdateRecord(ctx, msg.ConsumerId, *msg.UpdateRecord)
	return &types.MsgUpdateConsumerResponse{}, nil
}
