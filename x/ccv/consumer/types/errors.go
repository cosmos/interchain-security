package types

import (
	sdkerrors "cosmossdk.io/errors"
)

// Consumer sentinel errors
var (
	ErrNoProposerChannelID = sdkerrors.Register(ModuleName, 1, "no established CCV channel")
)
