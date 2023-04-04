package types

import errorsmod "cosmossdk.io/errors"

// Consumer sentinel errors
var (
	ErrNoProposerChannelID = errorsmod.Register(ModuleName, 1, "no established CCV channel")
)
