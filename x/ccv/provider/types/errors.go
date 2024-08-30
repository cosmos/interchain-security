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
	ErrInvalidConsumerId                       = errorsmod.Register(ModuleName, 6, "invalid consumer id")
	ErrConsumerKeyInUse                        = errorsmod.Register(ModuleName, 10, "consumer key is already in use by a validator")
	ErrCannotAssignDefaultKeyAssignment        = errorsmod.Register(ModuleName, 11, "cannot re-assign default key assignment")
	ErrInvalidConsumerRewardDenom              = errorsmod.Register(ModuleName, 14, "invalid consumer reward denom")
	ErrInvalidConsumerClient                   = errorsmod.Register(ModuleName, 16, "ccv channel is not built on correct client")
	ErrConsumerChainNotFound                   = errorsmod.Register(ModuleName, 18, "consumer chain not found")
	ErrCannotOptOutFromTopN                    = errorsmod.Register(ModuleName, 20, "cannot opt out from a Top N chain")
	ErrInvalidConsumerModificationProposal     = errorsmod.Register(ModuleName, 22, "invalid consumer modification proposal")
	ErrNoUnbondingTime                         = errorsmod.Register(ModuleName, 23, "provider unbonding time not found")
	ErrUnauthorized                            = errorsmod.Register(ModuleName, 25, "unauthorized")
	ErrBlankConsumerChainID                    = errorsmod.Register(ModuleName, 26, "consumer chain id must not be blank")
	ErrInvalidPhase                            = errorsmod.Register(ModuleName, 27, "cannot perform action in the current phase of consumer chain")
	ErrInvalidConsumerMetadata                 = errorsmod.Register(ModuleName, 28, "invalid consumer metadata")
	ErrInvalidPowerShapingParameters           = errorsmod.Register(ModuleName, 29, "invalid power shaping parameters")
	ErrInvalidConsumerInitializationParameters = errorsmod.Register(ModuleName, 30, "invalid consumer initialization parameters")
	ErrCannotUpdateMinimumPowerInTopN          = errorsmod.Register(ModuleName, 31, "cannot update minimum power in Top N")
	ErrNoConsumerGenesis                       = errorsmod.Register(ModuleName, 33, "missing consumer genesis")
	ErrInvalidConsumerGenesis                  = errorsmod.Register(ModuleName, 34, "invalid consumer genesis")
	ErrNoConsumerId                            = errorsmod.Register(ModuleName, 35, "missing consumer id")
	ErrAlreadyOptedIn                          = errorsmod.Register(ModuleName, 36, "already opted in to a chain with the same chain id")
	ErrNoOwnerAddress                          = errorsmod.Register(ModuleName, 37, "missing owner address")
	ErrInvalidNewOwnerAddress                  = errorsmod.Register(ModuleName, 38, "invalid new owner address")
	ErrInvalidTransformToTopN                  = errorsmod.Register(ModuleName, 39, "invalid transform to Top N chain")
	ErrInvalidTransformToOptIn                 = errorsmod.Register(ModuleName, 40, "invalid transform to Opt In chain")
	ErrCannotCreateTopNChain                   = errorsmod.Register(ModuleName, 41, "cannot create Top N chain outside permissionlessly")
	ErrCannotPrepareForLaunch                  = errorsmod.Register(ModuleName, 42, "cannot prepare chain for launch")
	ErrInvalidStopTime                         = errorsmod.Register(ModuleName, 43, "invalid stop time")
	ErrInvalidMsgCreateConsumer                = errorsmod.Register(ModuleName, 44, "invalid create consumer message")
	ErrInvalidMsgUpdateConsumer                = errorsmod.Register(ModuleName, 45, "invalid update consumer message")
	ErrInvalidMsgAssignConsumerKey             = errorsmod.Register(ModuleName, 46, "invalid assign consumer key message")
	ErrInvalidMsgSubmitConsumerMisbehaviour    = errorsmod.Register(ModuleName, 47, "invalid submit consumer misbehaviour message")
	ErrInvalidMsgSubmitConsumerDoubleVoting    = errorsmod.Register(ModuleName, 48, "invalid submit consumer double voting message")
	ErrInvalidMsgOptIn                         = errorsmod.Register(ModuleName, 49, "invalid opt in message")
	ErrInvalidMsgOptOut                        = errorsmod.Register(ModuleName, 50, "invalid opt out message")
	ErrInvalidMsgSetConsumerCommissionRate     = errorsmod.Register(ModuleName, 51, "invalid set consumer commission rate message")
)
