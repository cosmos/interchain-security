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
// then handles and returns the new bonded validators
func (k Keeper) ApplyCCValidatorChanges(ctx sdk.Context, changes []abci.ValidatorUpdate) (newVals []types.CrossChainValidator, err error) {
	for _, change := range changes {
		addr := utils.GetChangePubKeyAddress(change)
		val, found := k.GetCCValidator(ctx, utils.GetChangePubKeyAddress(change))

		// filter unbonding validators
		if change.Power < 1 {
			if found {
				k.DeleteCCValidator(ctx, val.Address)
				continue
			}
			return nil, fmt.Errorf("failed to find validator %s ", sdk.ConsAddress(addr))
		}

		// update bonded validators
		if !found {
			val = *types.NewCCValidator(change)
			newVals = append(newVals, val)
		} else {
			val.ValidatorUpdate = change
		}

		k.SetCCValidator(ctx, val)
	}

	// handle the new bonded validators
	if len(newVals) > 0 {
		err = k.HandleCCValidatorsBonded(ctx, newVals)
		if err != nil {
			return nil, err
		}
	}

	return
}

// HandleCCValidatorsBonded handles the given cross-chain validators newly bonded
func (k Keeper) HandleCCValidatorsBonded(ctx sdk.Context, newVals []types.CrossChainValidator) error {
	for _, v := range newVals {
		consAddr := sdk.ConsAddress(v.Address)
		// check that the cross-chain validator exists
		if _, found := k.GetCCValidator(ctx, v.Address); found {
			k.AfterValidatorBonded(ctx, consAddr, nil)
		} else {
			return fmt.Errorf("new validator unfound in cross-chain validator states")
		}
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
	return k.OutstandingPenalty(ctx, addr.Bytes())
}

// ValidatorByConsAddr returns an empty validator
func (k Keeper) ValidatorByConsAddr(sdk.Context, sdk.ConsAddress) stakingtypes.ValidatorI {
	return stakingtypes.Validator{}
}

// Slash sends a slashing request to the provider chain
// if the penalty flag for the given validator address is set to false
func (k Keeper) Slash(ctx sdk.Context, addr sdk.ConsAddress, infractionHeight, power int64, slashFraction sdk.Dec) {

	// check that the penalty flag is not set
	if k.OutstandingPenalty(ctx, addr) {
		return
	}

	// get current valset update ID
	// TODO: use pending penalty when channel not established yet
	valsetUpdateID := k.HeightToValsetUpdateID(ctx, uint64(infractionHeight))
	if valsetUpdateID < 1 {
		return
	}

	// send penalties
	k.SendPenalties(
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
	k.SetOutstandingPenalty(ctx, addr)
}

func (k Keeper) Unjail(sdk.Context, sdk.ConsAddress) {}

func (k Keeper) Delegation(sdk.Context, sdk.AccAddress, sdk.ValAddress) stakingtypes.DelegationI {
	panic("unimplemented on CCV keeper")
}

func (k Keeper) MaxValidators(sdk.Context) uint32 {
	panic("unimplemented on CCV keeper")
}
