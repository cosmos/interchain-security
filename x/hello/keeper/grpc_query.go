package keeper

import (
	"hello/x/hello/types"
)

var _ types.QueryServer = Keeper{}
