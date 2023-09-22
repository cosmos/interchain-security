package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	evidencetypes "github.com/cosmos/cosmos-sdk/x/evidence/types"

	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	"github.com/cosmos/interchain-security/v2/x/ccv/provider/types"
	"time"
)

// JailAndTombstoneValidator jails and tombstones the validator with the given provider consensus address
func (k Keeper) JailAndTombstoneValidator(ctx sdk.Context, providerAddr types.ProviderConsAddress) {
	logger := k.Logger(ctx)

	// get validator
	val, ok := k.stakingKeeper.GetValidatorByConsAddr(ctx, providerAddr.ToSdkConsAddr())
	if !ok || val.IsUnbonded() {
		logger.Error("validator not found or is unbonded", "provider consensus address", providerAddr.String())
		return
	}

	// check that the validator isn't tombstoned
	if k.slashingKeeper.IsTombstoned(ctx, providerAddr.ToSdkConsAddr()) {
		logger.Info("validator is already tombstoned", "provider consensus address", providerAddr.String())
		return
	}

	// jail validator if not already
	if !val.IsJailed() {
		k.stakingKeeper.Jail(ctx, providerAddr.ToSdkConsAddr())
	}

	// Jail the validator to trigger the unbonding of the validator
	// (see cosmos/cosmos-sdk/blob/v0.45.16-ics-lsm/x/staking/keeper/val_state_change.go#L192).
	k.slashingKeeper.JailUntil(ctx, providerAddr.ToSdkConsAddr(), evidencetypes.DoubleSignJailEndTime)

	// Tombstone the validator so that we cannot slash the validator more than once
	// (see cosmos/cosmos-sdk/blob/v0.45.16-ics-lsm/x/evidence/keeper/infraction.go#L81).
	// Note that we cannot simply use the fact that a validator is jailed to avoid slashing more than once
	// because then a validator could i) perform an equivocation, ii) get jailed (e.g., through downtime)
	// and in such a case the validator would not get slashed when we call `SlashValidator`.
	k.slashingKeeper.Tombstone(ctx, providerAddr.ToSdkConsAddr())
}

// ComputePowerToSlash computes the power to be slashed based on the tokens in non-matured (based on the
// provider `now` time) `undelegations` and `redelegations`, as well as the current `power` of the validator
func (k Keeper) ComputePowerToSlash(now time.Time, undelegations []stakingtypes.UnbondingDelegation,
	redelegations []stakingtypes.Redelegation, power int64, powerReduction sdk.Int) int64 {

	// compute the total numbers of tokens currently being undelegated
	undelegationsInTokens := sdk.NewInt(0)
	for _, u := range undelegations {
		for _, entry := range u.Entries {
			if entry.IsMature(now) && !entry.OnHold() {
				//  undelegation no longer eligible for slashing, skip it
				continue
			}
			undelegationsInTokens = undelegationsInTokens.Add(entry.InitialBalance)
		}
	}

	// compute the total numbers of tokens currently being redelegated
	redelegationsInTokens := sdk.NewInt(0)
	for _, r := range redelegations {
		for _, entry := range r.Entries {
			if entry.IsMature(now) && !entry.OnHold() {
				//  redelegation no longer eligible for slashing, skip it
				continue
			}
			redelegationsInTokens = redelegationsInTokens.Add(entry.InitialBalance)
		}
	}

	// The power we pass to staking's keeper `Slash` method is the current power of the validator together with the total
	// power of all the currently undelegated and redelegated tokens (see docs/docs/adrs/adr-013-equivocation-slashing.md).
	undelegationsAndRedelegationsInPower := sdk.TokensToConsensusPower(
		undelegationsInTokens.Add(redelegationsInTokens), powerReduction)

	return power + undelegationsAndRedelegationsInPower
}

// SlashValidator slashes validator with `providerAddr`
func (k Keeper) SlashValidator(ctx sdk.Context, providerAddr types.ProviderConsAddress) {
	logger := k.Logger(ctx)

	validator, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, providerAddr.ToSdkConsAddr())
	if !found {
		logger.Error("validator not found", "provider consensus address", providerAddr.String())
		return
	}

	if validator.IsUnbonded() {
		logger.Info("validator is unbonded", "provider consensus address", providerAddr.String())
		return
	}

	if k.slashingKeeper.IsTombstoned(ctx, providerAddr.ToSdkConsAddr()) {
		logger.Info("validator is already tombstoned", "provider consensus address", providerAddr.String())
		return
	}

	undelegations := k.stakingKeeper.GetUnbondingDelegationsFromValidator(ctx, validator.GetOperator())
	redelegations := k.stakingKeeper.GetRedelegationsFromSrcValidator(ctx, validator.GetOperator())
	lastPower := k.stakingKeeper.GetLastValidatorPower(ctx, validator.GetOperator())
	powerReduction := k.stakingKeeper.PowerReduction(ctx)
	totalPower := k.ComputePowerToSlash(ctx.BlockHeader().Time, undelegations, redelegations, lastPower, powerReduction)
	slashFraction := k.slashingKeeper.SlashFractionDoubleSign(ctx)

	k.stakingKeeper.Slash(ctx, providerAddr.ToSdkConsAddr(), 0, totalPower, slashFraction, stakingtypes.DoubleSign)
}
