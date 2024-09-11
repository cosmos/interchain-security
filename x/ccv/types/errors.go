package types

import (
	errorsmod "cosmossdk.io/errors"
)

// CCV sentinel errors
var (
	ErrInvalidPacketData           = errorsmod.Register(ModuleName, 1, "invalid CCV packet data")
	ErrInvalidVersion              = errorsmod.Register(ModuleName, 2, "invalid CCV version")
	ErrInvalidChannelFlow          = errorsmod.Register(ModuleName, 3, "invalid message sent to channel end")
	ErrInvalidGenesis              = errorsmod.Register(ModuleName, 4, "invalid genesis state")
	ErrDuplicateChannel            = errorsmod.Register(ModuleName, 5, "CCV channel already exists")
	ErrInvalidVSCMaturedId         = errorsmod.Register(ModuleName, 6, "invalid vscId for VSC packet")
	ErrInvalidVSCMaturedTime       = errorsmod.Register(ModuleName, 7, "invalid maturity time for VSC packet")
	ErrInvalidHandshakeMetadata    = errorsmod.Register(ModuleName, 8, "invalid provider handshake metadata")
	ErrChannelNotFound             = errorsmod.Register(ModuleName, 9, "channel not found")
	ErrClientNotFound              = errorsmod.Register(ModuleName, 10, "client not found")
	ErrInvalidConsumerState        = errorsmod.Register(ModuleName, 11, "provider chain has invalid state for consumer chain")
	ErrInvalidConsumerClient       = errorsmod.Register(ModuleName, 12, "ccv channel is not built on correct client")
	ErrInvalidProposal             = errorsmod.Register(ModuleName, 13, "invalid proposal")
	ErrDuplicateConsumerChain      = errorsmod.Register(ModuleName, 14, "consumer chain already exists")
	ErrConsumerChainNotFound       = errorsmod.Register(ModuleName, 15, "consumer chain not found")
	ErrInvalidDoubleVotingEvidence = errorsmod.Register(ModuleName, 16, "invalid consumer double voting evidence")
	ErrStoreKeyNotFound            = errorsmod.Register(ModuleName, 17, "store key not found")
	ErrStoreUnmarshal              = errorsmod.Register(ModuleName, 18, "cannot unmarshal value from store")
)
