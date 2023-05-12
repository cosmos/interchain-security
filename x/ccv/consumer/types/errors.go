package types

import (
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
)

// Consumer sentinel errors
var (
	ErrNoProposerChannelId                  = sdkerrors.Register(ModuleName, 1, "no established CCV channel")
	ErrConsumerRewardDenomAlreadyRegistered = sdkerrors.Register(ModuleName, 2, "consumer reward denom already registered")
)
