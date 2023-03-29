package keeper

import (
	"context"

	tmstrings "github.com/cometbft/cometbft/libs/strings"
	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	cryptotypes "github.com/cosmos/cosmos-sdk/crypto/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"
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

	// make sure the consumer key is in the correct format
	consumerSDKPublicKey, ok := msg.ConsumerKey.GetCachedValue().(cryptotypes.PubKey)
	if !ok {
		return nil, sdkerrors.Wrapf(sdkerrors.ErrInvalidType, "Expecting cryptotypes.PubKey, got %T", consumerSDKPublicKey)
	}

	// make sure the consumer key type is supported
	cp := ctx.ConsensusParams()
	if cp != nil && cp.Validator != nil {
		if !tmstrings.StringInSlice(consumerSDKPublicKey.Type(), cp.Validator.PubKeyTypes) {
			return nil, sdkerrors.Wrapf(
				stakingtypes.ErrValidatorPubKeyTypeNotSupported,
				"got: %s, expected: %s", consumerSDKPublicKey.Type(), cp.Validator.PubKeyTypes,
			)
		}
	}

	consumerTMPublicKey, err := cryptocodec.ToTmProtoPublicKey(consumerSDKPublicKey)
	if err != nil {
		return nil, err
	}

	if err := k.Keeper.AssignConsumerKey(ctx, msg.ChainId, validator, consumerTMPublicKey); err != nil {
		return nil, err
	}
	k.Logger(ctx).Info("assigned consumer key",
		"consumer chainID", msg.ChainId,
		"validator operator addr", msg.ProviderAddr,
		"consumer pubkey", consumerSDKPublicKey.String(),
	)

	ctx.EventManager().EmitEvents(sdk.Events{
		sdk.NewEvent(
			ccvtypes.EventTypeAssignConsumerKey,
			sdk.NewAttribute(ccvtypes.AttributeProviderValidatorAddress, msg.ProviderAddr),
			sdk.NewAttribute(ccvtypes.AttributeConsumerConsensusPubKey, consumerSDKPublicKey.String()),
		),
	})

	return &types.MsgAssignConsumerKeyResponse{}, nil
}
