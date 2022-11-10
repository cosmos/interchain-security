package keeper

import (
	"context"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	cryptotypes "github.com/cosmos/cosmos-sdk/crypto/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	tmstrings "github.com/tendermint/tendermint/libs/strings"
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
func (k msgServer) AssignConsensusPublicKeyToConsumerChain(goCtx context.Context, msg *types.MsgAssignConsensusPublicKeyToConsumerChain) (*types.MsgAssignConsensusPublicKeyToConsumerChainResponse, error) {
	ctx := sdk.UnwrapSDKContext(goCtx)

	// It is possible to assign keys for consumer chains that are not yet approved.
	// TODO: In future, a mechanism will be added to limit assigning keys to chains
	// which are approved or pending approval, only.
	// Note that current attack potential is restricted because validators must sign
	// the transaction, and the chainID size is limited.

	providerValidatorAddr, err := sdk.ValAddressFromBech32(msg.ProviderValidatorAddress)
	if err != nil {
		return nil, err
	}

	// validator must already be registered
	validator, found := k.stakingKeeper.GetValidator(ctx, providerValidatorAddr)
	if !found {
		return nil, types.ErrNoValidatorFound
	}
	providerTMPublicKey, err := validator.TmConsPublicKey()
	if err != nil {
		return nil, err
	}

	consumerSDKPublicKey, ok := msg.ConsumerConsensusPubKey.GetCachedValue().(cryptotypes.PubKey)
	if !ok {
		return nil, sdkerrors.Wrapf(sdkerrors.ErrInvalidType, "Expecting cryptotypes.PubKey, got %T", consumerSDKPublicKey)
	}

	cp := ctx.ConsensusParams()
	if cp != nil && cp.Validator != nil {
		if !tmstrings.StringInSlice(consumerSDKPublicKey.Type(), cp.Validator.PubKeyTypes) {
			return nil, sdkerrors.Wrapf(
				types.ErrValidatorPubKeyTypeNotSupported,
				"got: %s, expected: %s", consumerSDKPublicKey.Type(), cp.Validator.PubKeyTypes,
			)
		}
	}

	consumerTMPublicKey, err := cryptocodec.ToTmProtoPublicKey(consumerSDKPublicKey)
	if err != nil {
		return nil, err
	}

	err = k.KeyAssignment(ctx, msg.ChainId).SetProviderPubKeyToConsumerPubKey(
		providerTMPublicKey,
		consumerTMPublicKey,
	)

	if err != nil {
		return nil, err
	}

	ctx.EventManager().EmitEvents(sdk.Events{
		sdk.NewEvent(
			types.EventTypeAssignConsensusPublicKeyToConsumerChain,
			sdk.NewAttribute(types.AttributeProviderValidatorAddress, msg.ProviderValidatorAddress),
			sdk.NewAttribute(types.AttributeConsumerConsensusPubKey, consumerSDKPublicKey.String()),
		),
	})

	return &types.MsgAssignConsensusPublicKeyToConsumerChainResponse{}, nil
}
