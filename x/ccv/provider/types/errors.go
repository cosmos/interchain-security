package types

import (
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
)

// Provider sentinel errors
var (
	ErrInvalidCreateProposal    = sdkerrors.Register(ModuleName, 1, "invalid create consumer chain proposal")
	ErrInvalidStopProposal      = sdkerrors.Register(ModuleName, 2, "invalid stop consumer chain proposal")
	ErrUnknownConsumerChainId   = sdkerrors.Register(ModuleName, 3, "no consumer chain with this chain id")
	ErrUnknownConsumerChannelId = sdkerrors.Register(ModuleName, 4, "no consumer chain with this channel id")
)
