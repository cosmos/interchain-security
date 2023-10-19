package keeper

import (
	"context"
	"encoding/base64"

	errorsmod "cosmossdk.io/errors"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	tmprotocrypto "github.com/cometbft/cometbft/proto/tendermint/crypto"

	"github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
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
			types.EventTypeAssignConsumerKey,
			sdk.NewAttribute(types.AttributeProviderValidatorAddress, msg.ProviderAddr),
			sdk.NewAttribute(types.AttributeConsumerConsensusPubKey, consumerTMPublicKey.String()),
		),
	})

	return &types.MsgAssignConsumerKeyResponse{}, nil
}
