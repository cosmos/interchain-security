package types

import (
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
)

// Provider sentinel errors
var (
	ErrInvalidConsumerAdditionProposal  = sdkerrors.Register(ModuleName, 1, "invalid consumer addition proposal")
	ErrInvalidConsumerRemovalProp       = sdkerrors.Register(ModuleName, 2, "invalid consumer removal proposal")
	ErrUnknownConsumerChainId           = sdkerrors.Register(ModuleName, 3, "no consumer chain with this chain id")
	ErrUnknownConsumerChannelId         = sdkerrors.Register(ModuleName, 4, "no consumer chain with this channel id")
	ErrInvalidConsumerConsensusPubKey   = sdkerrors.Register(ModuleName, 5, "empty consumer consensus public key")
	ErrBlankConsumerChainID             = sdkerrors.Register(ModuleName, 6, "consumer chain id must not be blank")
	ErrConsumerKeyNotFound              = sdkerrors.Register(ModuleName, 7, "consumer key not found")
	ErrNoValidatorConsumerAddress       = sdkerrors.Register(ModuleName, 8, "error getting validator consumer address")
	ErrNoValidatorProviderAddress       = sdkerrors.Register(ModuleName, 9, "error getting validator provider address")
	ErrConsumerKeyInUse                 = sdkerrors.Register(ModuleName, 10, "consumer key is already in use by a validator")
	ErrCannotAssignDefaultKeyAssignment = sdkerrors.Register(ModuleName, 11, "cannot re-assign default key assignment")
	ErrInvalidConsumerParams            = sdkerrors.Register(ModuleName, 12, "invalid consumer params")
	ErrInvalidProviderAddress           = sdkerrors.Register(ModuleName, 13, "invalid provider address")
)
