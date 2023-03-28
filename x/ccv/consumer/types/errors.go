package types

import (
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
)

// Consumer sentinel errors
var (
	ErrNoProposerChannelID = sdkerrors.Register(ModuleName, 1, "no established CCV channel")
)
