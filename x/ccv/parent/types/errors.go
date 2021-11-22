package types

import (
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
)

// Parent sentinel errors
var (
	ErrInvalidProposal = sdkerrors.Register(ModuleName, 1, "invalid create child chain proposal")
)
