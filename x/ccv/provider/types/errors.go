package types

import errorsmod "cosmossdk.io/errors"

// Provider sentinel errors
var (
	ErrInvalidConsumerAdditionProposal = errorsmod.Register(ModuleName, 1, "invalid consumer addition proposal")
	ErrInvalidConsumerRemovalProp      = errorsmod.Register(ModuleName, 2, "invalid consumer removal proposal")
	ErrUnknownConsumerChainID          = errorsmod.Register(ModuleName, 3, "no consumer chain with this chain id")
	ErrUnknownConsumerChannelID        = errorsmod.Register(ModuleName, 4, "no consumer chain with this channel id")
	ErrInvalidConsumerConsensusPubKey  = errorsmod.Register(ModuleName, 5, "empty consumer consensus public key")
	ErrBlankConsumerChainID            = errorsmod.Register(ModuleName, 6, "consumer chain id must not be blank")
	ErrConsumerKeyNotFound             = errorsmod.Register(ModuleName, 7, "consumer key not found")
	ErrNoValidatorConsumerAddress      = errorsmod.Register(ModuleName, 8, "error getting validator consumer address")
	ErrNoValidatorProviderAddress      = errorsmod.Register(ModuleName, 9, "error getting validator provider address")
	ErrConsumerKeyInUse                = errorsmod.Register(ModuleName, 10, "consumer key is already in use by a validator")
	ErrInvalidConsumerParams           = errorsmod.Register(ModuleName, 11, "invalid consumer params")
	ErrInvalidProviderAddress          = errorsmod.Register(ModuleName, 12, "invalid provider address")
)
