package types

import (
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
)

// CCV sentinel errors
var (
	ErrInvalidPacketData        = sdkerrors.Register(ModuleName, 2, "invalid CCV packet data")
	ErrInvalidPacketTimeout     = sdkerrors.Register(ModuleName, 3, "invalid packet timeout")
	ErrInvalidVersion           = sdkerrors.Register(ModuleName, 4, "invalid CCV version")
	ErrInvalidChannelFlow       = sdkerrors.Register(ModuleName, 5, "invalid message sent to channel end")
	ErrInvalidConsumerChain     = sdkerrors.Register(ModuleName, 6, "invalid consumer chain")
	ErrInvalidProviderChain     = sdkerrors.Register(ModuleName, 7, "invalid provider chain")
	ErrInvalidStatus            = sdkerrors.Register(ModuleName, 8, "invalid channel status")
	ErrInvalidGenesis           = sdkerrors.Register(ModuleName, 9, "invalid genesis state")
	ErrDuplicateChannel         = sdkerrors.Register(ModuleName, 10, "CCV channel already exists")
	ErrInvalidVSCMaturedId      = sdkerrors.Register(ModuleName, 11, "invalid vscId for VSC packet")
	ErrInvalidVSCMaturedTime    = sdkerrors.Register(ModuleName, 12, "invalid maturity time for VSC packet")
	ErrInvalidConsumerState     = sdkerrors.Register(ModuleName, 13, "provider chain has invalid state for consumer chain")
	ErrInvalidConsumerClient    = sdkerrors.Register(ModuleName, 14, "ccv channel is not built on correct client")
	ErrInvalidProposal          = sdkerrors.Register(ModuleName, 15, "invalid proposal")
	ErrInvalidHandshakeMetadata = sdkerrors.Register(ModuleName, 16, "invalid provider handshake metadata")
	ErrChannelNotFound          = sdkerrors.Register(ModuleName, 17, "channel not found")
	ErrClientNotFound           = sdkerrors.Register(ModuleName, 18, "client not found")
)
