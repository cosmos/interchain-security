package types

import (
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
)

// Provider sentinel errors
var (
	ErrInvalidProposal          = sdkerrors.Register(ModuleName, 1, "invalid create consumer chain proposal")
	ErrUnknownConsumerChainId   = sdkerrors.Register(ModuleName, 2, "no consumer chain with this chain id")
	ErrUnknownConsumerChannelId = sdkerrors.Register(ModuleName, 2, "no consumer chain with this channel id")
)
