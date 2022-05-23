package keeper

import (
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	"github.com/cosmos/interchain-security/x/ccv/consumer/types"
	"github.com/cosmos/interchain-security/x/ccv/utils"
	abci "github.com/tendermint/tendermint/abci/types"
)

// ApplyCCValidatorChanges applies the given changes to the cross-chain validators states
func (k Keeper) ApplyCCValidatorChanges(ctx sdk.Context, changes []abci.ValidatorUpdate) {
	for _, change := range changes {
		addr := utils.GetChangePubKeyAddress(change)
		val, found := k.GetCCValidator(ctx, addr)

		// set new validator bonded
		if !found {
			consAddr := sdk.ConsAddress(addr)
			if change.Power < 1 {
				panic(fmt.Errorf("new validator bonded with zero voting power: %s", consAddr))
			}
			k.SetCCValidator(ctx, types.NewCCValidator(addr, change.Power))
			k.AfterValidatorBonded(ctx, consAddr, nil)
			continue
		}

		// remove unbonding existing-validators
		if change.Power < 1 {
			k.DeleteCCValidator(ctx, addr)
			continue
		}

		// update existing validators power
		val.Power = change.Power
		k.SetCCValidator(ctx, val)
	}
}

// IterateValidators - unimplemented on CCV keeper
func (k Keeper) IterateValidators(sdk.Context, func(index int64, validator stakingtypes.ValidatorI) (stop bool)) {
	panic("unimplemented on CCV keeper")
}

// Validator - unimplemented on CCV keeper
func (k Keeper) Validator(ctx sdk.Context, addr sdk.ValAddress) stakingtypes.ValidatorI {
	panic("unimplemented on CCV keeper")
}

// IsJailed returns the outstanding slashing flag for the given validator adddress
func (k Keeper) IsValidatorJailed(ctx sdk.Context, addr sdk.ConsAddress) bool {
	return k.OutstandingDowntime(ctx, addr)
}

// ValidatorByConsAddr returns an empty validator
func (k Keeper) ValidatorByConsAddr(sdk.Context, sdk.ConsAddress) stakingtypes.ValidatorI {
	return stakingtypes.Validator{}
}

// Slash sends a slashing request to the provider chain
func (k Keeper) Slash(ctx sdk.Context, addr sdk.ConsAddress, infractionHeight, power int64, _ sdk.Dec, infraction stakingtypes.InfractionType) {
	if infraction == stakingtypes.InfractionEmpty {
		return
	}

	k.SendSlashPacket(
		ctx,
		abci.Validator{
			Address: addr.Bytes(),
			Power:   power},
		// get VSC ID for infraction height
		k.GetHeightValsetUpdateID(ctx, uint64(infractionHeight)),
		infraction,
	)
}

// Jail - unimplemented on CCV keeper
func (k Keeper) Jail(ctx sdk.Context, addr sdk.ConsAddress) {}

// Unjail - unimplemented on CCV keeper
func (k Keeper) Unjail(sdk.Context, sdk.ConsAddress) {}

// Delegation - unimplemented on CCV keeper
func (k Keeper) Delegation(sdk.Context, sdk.AccAddress, sdk.ValAddress) stakingtypes.DelegationI {
	panic("unimplemented on CCV keeper")
}

// MaxValidators - unimplemented on CCV keeper
func (k Keeper) MaxValidators(sdk.Context) uint32 {
	panic("unimplemented on CCV keeper")
}
