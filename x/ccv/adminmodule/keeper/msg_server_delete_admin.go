package keeper

import (
	"context"

	"fmt"

	"github.com/cosmos/cosmos-sdk/store/prefix"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/x/ccv/adminmodule/types"
)

func (k msgServer) DeleteAdmin(goCtx context.Context, msg *types.MsgDeleteAdmin) (*types.MsgDeleteAdminResponse, error) {
	ctx := sdk.UnwrapSDKContext(goCtx)

	store := prefix.NewStore(ctx.KVStore(k.storeKey), []byte(types.AdminKey))

	storeCreator := store.Get([]byte(msg.Creator))
	if storeCreator == nil {
		return nil, fmt.Errorf("requester %s must be admin to delete admins", msg.Creator)
	}

	err := k.RemoveAdmin(ctx, msg.GetAdmin())
	if err != nil {
		return nil, err
	}

	return &types.MsgDeleteAdminResponse{}, nil
}
