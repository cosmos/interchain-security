package keeper

import (
	"context"
	"crypto/ed25519"
	"encoding/base64"

	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"
	tmprotocrypto "github.com/tendermint/tendermint/proto/tendermint/crypto"
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

	pubKeyBytes, err := base64.StdEncoding.DecodeString(msg.ConsumerKey)
	if err != nil {
		return nil, err
	}

	// make sure consumer key is correct ed25519 size
	if len(pubKeyBytes) != ed25519.PublicKeySize {
		return nil, sdkerrors.Wrapf(
			sdkerrors.ErrInvalidPubKey,
			"invalid consumer pub key len, got: %d, expected: %d", len(msg.ConsumerKey), ed25519.PublicKeySize,
		)
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
