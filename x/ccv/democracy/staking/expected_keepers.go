package staking

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
)

// ConsumerKeeper defines the contract needed to be fulfilled for staking module.
type ConsumerKeeper interface {
	GetParams(ctx sdk.Context) consumertypes.Params
}
