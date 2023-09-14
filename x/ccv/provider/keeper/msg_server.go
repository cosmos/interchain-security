package keeper

import (
	"context"
	"encoding/base64"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"

	errorsmod "cosmossdk.io/errors"
	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	"github.com/cosmos/interchain-security/v2/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v2/x/ccv/types"
	tmprotocrypto "github.com/tendermint/tendermint/proto/tendermint/crypto"
	tmtypes "github.com/tendermint/tendermint/types"
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

// CreateValidator defines a method for creating a new validator
func (k msgServer) AssignConsumerKey(goCtx context.Context, msg *types.MsgAssignConsumerKey) (*types.MsgAssignConsumerKeyResponse, error) {
	ctx := sdk.UnwrapSDKContext(goCtx)

	// It is possible to assign keys for consumer chains that are not yet approved.
	// TODO: In future, a mechanism will be added to limit assigning keys to chains
	// which are approved or pending approval, only.
	// Note that current attack potential is restricted because validators must sign
	// the transaction, and the chainID size is limited.

	providerValidatorAddr, err := sdk.ValAddressFromBech32(msg.ProviderAddr)
	if err != nil {
		return nil, err
	}

	// validator must already be registered
	validator, found := k.stakingKeeper.GetValidator(ctx, providerValidatorAddr)
	if !found {
		return nil, stakingtypes.ErrNoValidatorFound
	}

	// parse consumer key as long as it's in the right format
	pkType, keyStr, err := types.ParseConsumerKeyFromJson(msg.ConsumerKey)
	if err != nil {
		return nil, err
	}

	// Note: the correct way to decide if a key type is supported is to check the
	// consensus params. However this functionality was disabled in https://github.com/cosmos/interchain-security/pull/916
	// as a quick way to get ed25519 working, avoiding amino/proto-any marshalling issues.

	// make sure the consumer key type is supported
	// cp := ctx.ConsensusParams()
	// if cp != nil && cp.Validator != nil {
	// 	if !tmstrings.StringInSlice(pkType, cp.Validator.PubKeyTypes) {
	// 		return nil, errorsmod.Wrapf(
	// 			stakingtypes.ErrValidatorPubKeyTypeNotSupported,
	// 			"got: %s, expected one of: %s", pkType, cp.Validator.PubKeyTypes,
	// 		)
	// 	}
	// }

	// For now, only accept ed25519.
	// TODO: decide what types should be supported.
	if pkType != "/cosmos.crypto.ed25519.PubKey" {
		return nil, errorsmod.Wrapf(
			stakingtypes.ErrValidatorPubKeyTypeNotSupported,
			"got: %s, expected: %s", pkType, "/cosmos.crypto.ed25519.PubKey",
		)
	}

	pubKeyBytes, err := base64.StdEncoding.DecodeString(keyStr)
	if err != nil {
		return nil, err
	}

	consumerTMPublicKey := tmprotocrypto.PublicKey{
		Sum: &tmprotocrypto.PublicKey_Ed25519{
			Ed25519: pubKeyBytes,
		},
	}

	if err := k.Keeper.AssignConsumerKey(ctx, msg.ChainId, validator, consumerTMPublicKey); err != nil {
		return nil, err
	}
	k.Logger(ctx).Info("assigned consumer key",
		"consumer chainID", msg.ChainId,
		"validator operator addr", msg.ProviderAddr,
		"consumer tm pubkey", consumerTMPublicKey.String(),
	)

	ctx.EventManager().EmitEvents(sdk.Events{
		sdk.NewEvent(
			ccvtypes.EventTypeAssignConsumerKey,
			sdk.NewAttribute(ccvtypes.AttributeProviderValidatorAddress, msg.ProviderAddr),
			sdk.NewAttribute(ccvtypes.AttributeConsumerConsensusPubKey, consumerTMPublicKey.String()),
		),
	})

	return &types.MsgAssignConsumerKeyResponse{}, nil
}

func (k msgServer) RegisterConsumerRewardDenom(goCtx context.Context, msg *types.MsgRegisterConsumerRewardDenom) (*types.MsgRegisterConsumerRewardDenomResponse, error) {
	ctx := sdk.UnwrapSDKContext(goCtx)

	depositer, err := sdk.AccAddressFromBech32(msg.Depositor)
	if err != nil {
		return nil, err
	}

	if err := k.Keeper.RegisterConsumerRewardDenom(ctx, msg.Denom, depositer); err != nil {
		return nil, err
	}

	ctx.EventManager().EmitEvent(sdk.NewEvent(
		ccvtypes.EventTypeRegisterConsumerRewardDenom,
		sdk.NewAttribute(ccvtypes.AttributeConsumerRewardDenom, msg.Denom),
		sdk.NewAttribute(ccvtypes.AttributeConsumerRewardDepositor, msg.Depositor),
	))

	return &types.MsgRegisterConsumerRewardDenomResponse{}, nil
}

func (k msgServer) SubmitConsumerMisbehaviour(goCtx context.Context, msg *types.MsgSubmitConsumerMisbehaviour) (*types.MsgSubmitConsumerMisbehaviourResponse, error) {
	ctx := sdk.UnwrapSDKContext(goCtx)
	if err := k.Keeper.HandleConsumerMisbehaviour(ctx, *msg.Misbehaviour); err != nil {
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

	// handle the double voting evidence using the chain ID of the infraction block header
	// and the malicious validator's public key
	if err := k.Keeper.HandleConsumerDoubleVoting(ctx, evidence, msg.InfractionBlockHeader.Header.ChainID, pubkey); err != nil {
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
