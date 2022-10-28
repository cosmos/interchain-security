package keeper

import (
	"context"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
)

type msgServer struct {
	Keeper
}

// NewMsgServerImpl returns an implementation of the bank MsgServer interface
// for the provided Keeper.
func NewMsgServerImpl(keeper Keeper) types.MsgServer {
	return &msgServer{Keeper: keeper}
}

var _ types.MsgServer = msgServer{}

// CreateValidator defines a method for creating a new validator
func (k msgServer) DesignateConsensusKeyForConsumerChain(goCtx context.Context, msg *types.MsgDesignateConsensusKeyForConsumerChain) (*types.MsgDesignateConsensusKeyForConsumerChainResponse, error) {
	ctx := sdk.UnwrapSDKContext(goCtx)
	_ = ctx

	// TODO:

	return &types.MsgDesignateConsensusKeyForConsumerChainResponse{}, nil
}
