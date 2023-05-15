package types

import (
	errorsmod "cosmossdk.io/errors"
)

// Consumer sentinel errors
var (
	ErrNoProposerChannelId                  = errorsmod.Register(ModuleName, 1, "no established CCV channel")
	ErrConsumerRewardDenomAlreadyRegistered = errorsmod.Register(ModuleName, 2, "consumer reward denom already registered")
)
