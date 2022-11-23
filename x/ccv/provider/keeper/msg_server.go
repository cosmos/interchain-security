package keeper

import (
	"context"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	cryptotypes "github.com/cosmos/cosmos-sdk/crypto/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"
	utils "github.com/cosmos/interchain-security/x/ccv/utils"
	abci "github.com/tendermint/tendermint/abci/types"
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
func (k msgServer) AssignConsumerKey(goCtx context.Context, msg *types.MsgAssignConsumerKey) (*types.MsgAssignConsumerKeyResponse, error) {
	ctx := sdk.UnwrapSDKContext(goCtx)

	// It is possible to assign keys for consumer chains that are not yet approved.
	// TODO: In future, a mechanism will be added to limit assigning keys to chains
	// which are approved or pending approval, only.
	// Note that current attack potential is restricted because validators must sign
	// the transaction, and the chainID size is limited.

	providerAddr, err := sdk.ConsAddressFromBech32(msg.ProviderAddr)
	if err != nil {
		return nil, err
	}

	// validator must already be registered
	validator, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, providerAddr)
	if !found {
		return nil, stakingtypes.ErrNoValidatorFound
	}

	// check if the consumer chain is registered, i.e.,
	// a client to the consumer was already created
	_, consumerRegistered := k.GetConsumerClientId(ctx, msg.ChainId)

	// get the previous key assigned for this validator on this consumer chain
	oldConsumerKey, found := k.GetValidatorConsumerPubKey(ctx, msg.ChainId, providerAddr)
	if !found {
		// the validator had no key assigned on this consumer chain
		oldConsumerKey, err = validator.TmConsPublicKey()
		if err != nil {
			return nil, err
		}
	} else {
		oldConsumerAddr := utils.TMCryptoPublicKeyToConsAddr(oldConsumerKey)
		if consumerRegistered {
			// mark this old consumer key as prunable once the VSCMaturedPacket
			// for the current VSC ID is received;
			// note: this state is removed on receiving the VSCMaturedPacket
			k.AppendConsumerValidatorByVscID(
				ctx,
				msg.ChainId,
				k.GetValidatorSetUpdateId(ctx),
				oldConsumerAddr,
			)
		} else {
			// no VSCPacket will be sent for this chain in EndBlock,
			// thus prune the old consumer key directly
			k.DeleteValidatorByConsumerAddr(ctx, msg.ChainId, oldConsumerAddr)
		}
	}

	// get the previous power of this validator
	oldPower := k.stakingKeeper.GetLastValidatorPower(ctx, sdk.ValAddress(validator.OperatorAddress))
	// if the validator is active and the consumer is registered,
	// then store old key and power for modifying the valset update in EndBlock;
	// note: this state is deleted at the end of the block
	if oldPower > 0 && consumerRegistered {
		k.SetPendingKeyAssignment(
			ctx,
			msg.ChainId,
			providerAddr,
			abci.ValidatorUpdate{PubKey: oldConsumerKey, Power: oldPower},
		)
	}

	// set the mapping from this validator's provider address to the new consumer key;
	// overwrite if already exists
	consumerSDKPublicKey, ok := msg.ConsumerKey.GetCachedValue().(cryptotypes.PubKey)
	if !ok {
		return nil, sdkerrors.Wrapf(sdkerrors.ErrInvalidType, "Expecting cryptotypes.PubKey, got %T", consumerSDKPublicKey)
	}
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
	// note: this state is deleted when the validator is removed from the staking module
	k.SetValidatorConsumerPubKey(ctx, msg.ChainId, providerAddr, consumerTMPublicKey)

	// if the consumer chain is already registered, set the mapping from
	// this validator's new consensus address on the consumer
	// to its consensus address on the provider;
	// otherwise, the mapping is added when the consumer is registered
	if consumerRegistered {
		consumerAddr := utils.TMCryptoPublicKeyToConsAddr(consumerTMPublicKey)
		if _, found := k.GetValidatorByConsumerAddr(ctx, msg.ChainId, consumerAddr); found {
			// mapping already exists; return error
			return nil, sdkerrors.Wrapf(
				types.ErrInvalidConsumerConsensusPubKey, "consumer key already exists",
			)
		}
		// note: this state must be deleted through the pruning mechanism;
		// see ConsumerValidatorsByVscID
		k.SetValidatorByConsumerAddr(ctx, msg.ChainId, consumerAddr, providerAddr)
	}

	ctx.EventManager().EmitEvents(sdk.Events{
		sdk.NewEvent(
			ccvtypes.EventTypeAssignConsumerKey,
			sdk.NewAttribute(ccvtypes.AttributeProviderValidatorAddress, msg.ProviderAddr),
			sdk.NewAttribute(ccvtypes.AttributeConsumerConsensusPubKey, consumerSDKPublicKey.String()),
		),
	})

	return &types.MsgAssignConsumerKeyResponse{}, nil
}
