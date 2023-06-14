package types

import (
	errorsmod "cosmossdk.io/errors"
)

// CCV sentinel errors
var (
	ErrInvalidPacketData        = errorsmod.Register(ModuleName, 2, "invalid CCV packet data")
	ErrInvalidPacketTimeout     = errorsmod.Register(ModuleName, 3, "invalid packet timeout")
	ErrInvalidVersion           = errorsmod.Register(ModuleName, 4, "invalid CCV version")
	ErrInvalidChannelFlow       = errorsmod.Register(ModuleName, 5, "invalid message sent to channel end")
	ErrInvalidConsumerChain     = errorsmod.Register(ModuleName, 6, "invalid consumer chain")
	ErrInvalidProviderChain     = errorsmod.Register(ModuleName, 7, "invalid provider chain")
	ErrInvalidStatus            = errorsmod.Register(ModuleName, 8, "invalid channel status")
	ErrInvalidGenesis           = errorsmod.Register(ModuleName, 9, "invalid genesis state")
	ErrDuplicateChannel         = errorsmod.Register(ModuleName, 10, "CCV channel already exists")
	ErrInvalidVSCMaturedId      = errorsmod.Register(ModuleName, 11, "invalid vscId for VSC packet")
	ErrInvalidVSCMaturedTime    = errorsmod.Register(ModuleName, 12, "invalid maturity time for VSC packet")
	ErrInvalidConsumerState     = errorsmod.Register(ModuleName, 13, "provider chain has invalid state for consumer chain")
	ErrInvalidConsumerClient    = errorsmod.Register(ModuleName, 14, "ccv channel is not built on correct client")
	ErrInvalidProposal          = errorsmod.Register(ModuleName, 15, "invalid proposal")
	ErrInvalidHandshakeMetadata = errorsmod.Register(ModuleName, 16, "invalid provider handshake metadata")
	ErrChannelNotFound          = errorsmod.Register(ModuleName, 17, "channel not found")
	ErrClientNotFound           = errorsmod.Register(ModuleName, 18, "client not found")
	ErrDuplicateConsumerChain   = errorsmod.Register(ModuleName, 19, "consumer chain already exists")
	ErrConsumerChainNotFound    = errorsmod.Register(ModuleName, 20, "consumer chain not found")
)
