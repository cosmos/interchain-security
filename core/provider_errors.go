package core

import (
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
)

// Provider sentinel errors
var (
	ErrInvalidConsumerAdditionProposal  = sdkerrors.Register(ProviderModuleName, 1, "invalid consumer addition proposal")
	ErrInvalidConsumerRemovalProp       = sdkerrors.Register(ProviderModuleName, 2, "invalid consumer removal proposal")
	ErrUnknownConsumerChainId           = sdkerrors.Register(ProviderModuleName, 3, "no consumer chain with this chain id")
	ErrUnknownConsumerChannelId         = sdkerrors.Register(ProviderModuleName, 4, "no consumer chain with this channel id")
	ErrInvalidConsumerConsensusPubKey   = sdkerrors.Register(ProviderModuleName, 5, "empty consumer consensus public key")
	ErrBlankConsumerChainID             = sdkerrors.Register(ProviderModuleName, 6, "consumer chain id must not be blank")
	ErrConsumerKeyNotFound              = sdkerrors.Register(ProviderModuleName, 7, "consumer key not found")
	ErrNoValidatorConsumerAddress       = sdkerrors.Register(ProviderModuleName, 8, "error getting validator consumer address")
	ErrNoValidatorProviderAddress       = sdkerrors.Register(ProviderModuleName, 9, "error getting validator provider address")
	ErrConsumerKeyInUse                 = sdkerrors.Register(ProviderModuleName, 10, "consumer key is already in use by a validator")
	ErrCannotAssignDefaultKeyAssignment = sdkerrors.Register(ProviderModuleName, 11, "cannot re-assign default key assignment")
	ErrInvalidConsumerParams            = sdkerrors.Register(ProviderModuleName, 12, "invalid consumer params")
	ErrInvalidProviderAddress           = sdkerrors.Register(ProviderModuleName, 13, "invalid provider address")
)
