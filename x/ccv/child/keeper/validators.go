package keeper

import (
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	"github.com/cosmos/interchain-security/x/ccv/child/types"
	"github.com/cosmos/interchain-security/x/ccv/utils"
	abci "github.com/tendermint/tendermint/abci/types"
)

// ApplyCCValidatorChanges applies the given changes to the cross-chain validators states
func (k Keeper) ApplyCCValidatorChanges(ctx sdk.Context, changes []abci.ValidatorUpdate) error {
	for _, change := range changes {
		addr := utils.GetChangePubKeyAddress(change)
		val, found := k.GetCCValidator(ctx, addr)

		// set new validator bonded
		if !found {
			consAddr := sdk.ConsAddress(addr)
			if change.Power < 1 {
				return fmt.Errorf("failed to find validator: %s", consAddr)
			}
			k.SetCCValidator(ctx, types.NewCCValidator(change))
			k.AfterValidatorBonded(ctx, consAddr, nil)
			continue
		}

		// remove unbonding existing-validators
		if change.Power < 1 {
			if found {
				k.DeleteCCValidator(ctx, addr)
			}
			continue
		}

		// update existing validators power
		val.ValidatorUpdate.Power = change.Power
		k.SetCCValidator(ctx, val)
	}

	return nil
}

// IterateValidators - unimplemented on CCV keeper
func (k Keeper) IterateValidators(sdk.Context, func(index int64, validator stakingtypes.ValidatorI) (stop bool)) {
	panic("unimplemented on CCV keeper")
}

// Validator - unimplemented on CCV keeper
func (k Keeper) Validator(ctx sdk.Context, addr sdk.ValAddress) stakingtypes.ValidatorI {
	panic("unimplemented on CCV keeper")
}

// IsJailed returns the outstanding penalty flag for the given validator adddress
func (k Keeper) IsValidatorJailed(ctx sdk.Context, addr sdk.ConsAddress) bool {
	return k.OutstandingDowntime(ctx, addr)
}

// ValidatorByConsAddr returns an empty validator
func (k Keeper) ValidatorByConsAddr(sdk.Context, sdk.ConsAddress) stakingtypes.ValidatorI {
	return stakingtypes.Validator{}
}

// Slash sends a slashing request to the provider chain
// if the penalty flag for the given validator address is set to false
func (k Keeper) Slash(ctx sdk.Context, addr sdk.ConsAddress, infractionHeight, power int64, slashFraction sdk.Dec) {

	// check that the penalty flag is not set
	if k.OutstandingDowntime(ctx, addr) {
		return
	}

	// get current valset update ID
	// TODO: use pending penalty when channel not established yet
	valsetUpdateID := k.HeightToValsetUpdateID(ctx, uint64(infractionHeight))
	if valsetUpdateID < 1 {
		return
	}

	// send penalties
	k.SendSlashPacket(
		ctx,
		abci.Validator{
			Address: addr.Bytes(),
			Power:   power},
		valsetUpdateID,
		slashFraction.TruncateInt64(),
		k.slashingKeeper.DowntimeJailDuration(ctx).Nanoseconds(),
	)
}

// Jail sets the penalty flag to true for the given validator address
func (k Keeper) Jail(ctx sdk.Context, addr sdk.ConsAddress) {
	k.SetOutstandingDowntime(ctx, addr)
}

func (k Keeper) Unjail(sdk.Context, sdk.ConsAddress) {}

func (k Keeper) Delegation(sdk.Context, sdk.AccAddress, sdk.ValAddress) stakingtypes.DelegationI {
	panic("unimplemented on CCV keeper")
}

func (k Keeper) MaxValidators(sdk.Context) uint32 {
	panic("unimplemented on CCV keeper")
}
