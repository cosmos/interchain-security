package keeper

import (
	"github.com/cosmos/interchain-security/x/ccv/adminmodule/types"
)

type msgServer struct {
	Keeper
}

// NewMsgServerImpl returns an implementation of the MsgServer interface
// for the provided Keeper.
func NewMsgServerImpl(k Keeper) types.MsgServer {
	return &msgServer{Keeper: k}
}

var _ types.MsgServer = msgServer{}
