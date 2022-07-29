package keeper

import (
	"github.com/cosmos/interchain-security/x/hello/types"
)

var _ types.QueryServer = Keeper{}
