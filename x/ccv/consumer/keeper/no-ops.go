package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/x/staking/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
)

// fulfills all the no-ops of staking keeper

// Load the last total validator power.
func (k *Keeper) GetLastTotalPower(ctx sdk.Context) sdk.Int {
	return sdk.Int{}
}

// TODO: confirm OK to stub
// Set the last total validator power.
func (k *Keeper) SetLastTotalPower(ctx sdk.Context, power sdk.Int) {}

// TODO: this is only used as part of IBC test framework, ok to stub?
// Delegate performs a delegation, set/update everything necessary within the store.
// tokenSrc indicates the bond status of the incoming funds.
func (k Keeper) Delegate(
	ctx sdk.Context, delAddr sdk.AccAddress, bondAmt sdk.Int, tokenSrc types.BondStatus,
	validator types.Validator, subtractAccount bool,
) (newShares sdk.Dec, err error) {
	return sdk.Dec{}, nil
}

// TODO: this is only used as part of IBC test framework, ok to stub?
// return a given amount of all the validators
func (k Keeper) GetValidators(ctx sdk.Context, maxRetrieve uint32) (validators []stakingtypes.Validator) {
	return nil
}
