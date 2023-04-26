package types

import (
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
)

// Consumer sentinel errors
var (
	ErrNoProposerChannelId = sdkerrors.Register(ConsumerModuleName, 1, "no established CCV channel")
)
