package keeper

import (
	"context"

	"fmt"

	"github.com/cosmos/cosmos-sdk/store/prefix"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/x/ccv/adminmodule/types"
)

func (k msgServer) AddAdmin(goCtx context.Context, msg *types.MsgAddAdmin) (*types.MsgAddAdminResponse, error) {
	ctx := sdk.UnwrapSDKContext(goCtx)

	store := prefix.NewStore(ctx.KVStore(k.storeKey), []byte(types.AdminKey))

	storeCreator := store.Get([]byte(msg.Creator))
	if storeCreator == nil {
		return nil, fmt.Errorf("requester %s must be admin to add admins", msg.Creator)
	}

	k.SetAdmin(ctx, msg.GetAdmin())

	return &types.MsgAddAdminResponse{}, nil
}
