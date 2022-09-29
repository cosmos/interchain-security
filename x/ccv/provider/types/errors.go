package types

import (
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
)

// Provider sentinel errors
var (
	ErrInvalidConsumerAdditionProposal = sdkerrors.Register(ModuleName, 1, "invalid consumer addition proposal")
	ErrInvalidConsumerRemovalProp      = sdkerrors.Register(ModuleName, 2, "invalid consumer removal proposal")
	ErrUnknownConsumerChainId          = sdkerrors.Register(ModuleName, 3, "no consumer chain with this chain id")
	ErrUnknownConsumerChannelId        = sdkerrors.Register(ModuleName, 4, "no consumer chain with this channel id")
)
