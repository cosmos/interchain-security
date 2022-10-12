package keeper

import (
	"github.com/cosmos/interchain-security/x/ccv/adminmodule/types"
)

var _ types.QueryServer = Keeper{}
