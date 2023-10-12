package types

import (
	errorsmod "cosmossdk.io/errors"
)

// CCV sentinel errors
var (
	ErrInvalidPacketData        = errorsmod.Register(ModuleName, 1, "invalid CCV packet data")
	ErrInvalidVersion           = errorsmod.Register(ModuleName, 2, "invalid CCV version")
	ErrInvalidChannelFlow       = errorsmod.Register(ModuleName, 3, "invalid message sent to channel end")
	ErrInvalidGenesis           = errorsmod.Register(ModuleName, 4, "invalid genesis state")
	ErrDuplicateChannel         = errorsmod.Register(ModuleName, 5, "CCV channel already exists")
	ErrInvalidVSCMaturedId      = errorsmod.Register(ModuleName, 6, "invalid vscId for VSC packet")
	ErrInvalidVSCMaturedTime    = errorsmod.Register(ModuleName, 7, "invalid maturity time for VSC packet")
	ErrInvalidHandshakeMetadata = errorsmod.Register(ModuleName, 8, "invalid provider handshake metadata")
	ErrChannelNotFound          = errorsmod.Register(ModuleName, 9, "channel not found")
	ErrClientNotFound           = errorsmod.Register(ModuleName, 10, "client not found")
)
