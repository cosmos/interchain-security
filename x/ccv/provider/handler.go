package provider

import (
	errorsmod "cosmossdk.io/errors"

	"github.com/cosmos/cosmos-sdk/baseapp"
	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"

	"github.com/cosmos/interchain-security/v4/x/ccv/provider/keeper"
	"github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
)

func NewHandler(k *keeper.Keeper) baseapp.MsgServiceHandler {
	msgServer := keeper.NewMsgServerImpl(k)

	return func(ctx sdk.Context, msg sdk.Msg) (*sdk.Result, error) {
		ctx = ctx.WithEventManager(sdk.NewEventManager())

		switch msg := msg.(type) {
		case *types.MsgAssignConsumerKey:
			res, err := msgServer.AssignConsumerKey(ctx, msg)
			return sdk.WrapServiceResult(ctx, res, err)
		case *types.MsgSubmitConsumerMisbehaviour:
			res, err := msgServer.SubmitConsumerMisbehaviour(ctx, msg)
			return sdk.WrapServiceResult(ctx, res, err)
		case *types.MsgSubmitConsumerDoubleVoting:
			res, err := msgServer.SubmitConsumerDoubleVoting(ctx, msg)
			return sdk.WrapServiceResult(ctx, res, err)
		default:
			return nil, errorsmod.Wrapf(sdkerrors.ErrUnknownRequest, "unrecognized %s message type: %T", types.ModuleName, msg)
		}
	}
}
