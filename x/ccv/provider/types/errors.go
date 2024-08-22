package types

import (
	errorsmod "cosmossdk.io/errors"
)

// Provider sentinel errors
var (
	ErrInvalidConsumerAdditionProposal         = errorsmod.Register(ModuleName, 1, "invalid consumer addition proposal")
	ErrInvalidConsumerRemovalProp              = errorsmod.Register(ModuleName, 2, "invalid consumer removal proposal")
	ErrUnknownConsumerId                       = errorsmod.Register(ModuleName, 3, "no consumer chain with this consumer id")
	ErrUnknownConsumerChannelId                = errorsmod.Register(ModuleName, 4, "no consumer chain with this channel id")
	ErrInvalidConsumerConsensusPubKey          = errorsmod.Register(ModuleName, 5, "empty consumer consensus public key")
	ErrInvalidConsumerId                       = errorsmod.Register(ModuleName, 6, "invalid consumer id")
	ErrConsumerKeyNotFound                     = errorsmod.Register(ModuleName, 7, "consumer key not found")
	ErrNoValidatorConsumerAddress              = errorsmod.Register(ModuleName, 8, "error getting validator consumer address")
	ErrNoValidatorProviderAddress              = errorsmod.Register(ModuleName, 9, "error getting validator provider address")
	ErrConsumerKeyInUse                        = errorsmod.Register(ModuleName, 10, "consumer key is already in use by a validator")
	ErrCannotAssignDefaultKeyAssignment        = errorsmod.Register(ModuleName, 11, "cannot re-assign default key assignment")
	ErrInvalidConsumerParams                   = errorsmod.Register(ModuleName, 12, "invalid consumer params")
	ErrInvalidProviderAddress                  = errorsmod.Register(ModuleName, 13, "invalid provider address")
	ErrInvalidConsumerRewardDenom              = errorsmod.Register(ModuleName, 14, "invalid consumer reward denom")
	ErrInvalidDepositorAddress                 = errorsmod.Register(ModuleName, 15, "invalid depositor address")
	ErrInvalidConsumerClient                   = errorsmod.Register(ModuleName, 16, "ccv channel is not built on correct client")
	ErrDuplicateConsumerChain                  = errorsmod.Register(ModuleName, 17, "consumer chain already exists")
	ErrConsumerChainNotFound                   = errorsmod.Register(ModuleName, 18, "consumer chain not found")
	ErrInvalidConsumerCommissionRate           = errorsmod.Register(ModuleName, 19, "consumer commission rate is invalid")
	ErrCannotOptOutFromTopN                    = errorsmod.Register(ModuleName, 20, "cannot opt out from a Top N chain")
	ErrNoUnconfirmedVSCPacket                  = errorsmod.Register(ModuleName, 21, "no unconfirmed vsc packet for this chain id")
	ErrInvalidConsumerModificationProposal     = errorsmod.Register(ModuleName, 22, "invalid consumer modification proposal")
	ErrNoUnbondingTime                         = errorsmod.Register(ModuleName, 23, "provider unbonding time not found")
	ErrInvalidAddress                          = errorsmod.Register(ModuleName, 24, "invalid address")
	ErrUnauthorized                            = errorsmod.Register(ModuleName, 25, "unauthorized")
	ErrBlankConsumerChainID                    = errorsmod.Register(ModuleName, 26, "consumer chain id must not be blank")
	ErrInvalidPhase                            = errorsmod.Register(ModuleName, 27, "cannot perform action in the current phase of consumer chain")
	ErrInvalidPowerShapingParameters           = errorsmod.Register(ModuleName, 28, "invalid power shaping parameters")
	ErrInvalidConsumerInitializationParameters = errorsmod.Register(ModuleName, 29, "invalid consumer initialization parameters")
	ErrNoRegistrationRecord                    = errorsmod.Register(ModuleName, 30, "registration record is missing")
	ErrNoChainId                               = errorsmod.Register(ModuleName, 31, "missing chain id for consumer chain")
	ErrNoConsumerGenesis                       = errorsmod.Register(ModuleName, 32, "missing consumer genesis")
	ErrInvalidConsumerGenesis                  = errorsmod.Register(ModuleName, 33, "invalid consumer genesis")
	ErrNoConsumerId                            = errorsmod.Register(ModuleName, 34, "missing consumer id")
	ErrAlreadyOptedIn                          = errorsmod.Register(ModuleName, 35, "already opted in to a chain with the same chain id")
	ErrNoOwnerAddress                          = errorsmod.Register(ModuleName, 36, "missing owner address")
	ErrInvalidTransformToTopN                  = errorsmod.Register(ModuleName, 37, "invalid transform to Top N chain")
)
