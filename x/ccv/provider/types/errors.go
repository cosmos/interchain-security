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
	ErrInvalidConsumerConsensusPubKey  = sdkerrors.Register(ModuleName, 5, "empty consumer consensus public key")
	ErrBlankConsumerChainID            = sdkerrors.Register(ModuleName, 6, "consumer chain id must not be blank")
	ErrConsumerKeyNotFound             = sdkerrors.Register(ModuleName, 7, "consumer key not found")
)
