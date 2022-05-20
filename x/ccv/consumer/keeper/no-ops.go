package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
)

// fulfills all the no-ops of staking keeper

// Load the last total validator power.
func (k *Keeper) GetLastTotalPower(ctx sdk.Context) sdk.Int {
	return sdk.Int{}
}

// TODO: confirm OK to stub
// Set the last total validator power.
func (k *Keeper) SetLastTotalPower(ctx sdk.Context, power sdk.Int) {}
