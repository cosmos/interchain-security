package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	evidencetypes "github.com/cosmos/cosmos-sdk/x/evidence/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	"github.com/cosmos/interchain-security/v2/x/ccv/provider/types"
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
	// (see cosmos/cosmos-sdk/blob/v0.47.0/x/staking/keeper/val_state_change.go#L194).
	k.slashingKeeper.JailUntil(ctx, providerAddr.ToSdkConsAddr(), evidencetypes.DoubleSignJailEndTime)

	// Tombstone the validator so that we cannot slash the validator more than once
	// (see cosmos/cosmos-sdk/blob/v0.47.0/x/evidence/keeper/infraction.go#L94).
	// Note that we cannot simply use the fact that a validator is jailed to avoid slashing more than once
	// because then a validator could i) perform an equivocation, ii) get jailed (e.g., through downtime)
	// and in such a case the validator would not get slashed when calling `SlashValidator`.
	// TODO: check if tombstone ... can it panic???
	k.slashingKeeper.Tombstone(ctx, providerAddr.ToSdkConsAddr())
}

func (k Keeper) ComputePowerToSlash(undelegations []stakingtypes.UnbondingDelegation,
	redelegations []stakingtypes.Redelegation, power int64, powerReduction sdk.Int) int64 {

	// compute the total numbers of tokens currently being undelegated
	undelegationsInTokens := sdk.NewInt(0)
	for _, u := range undelegations {
		for _, entry := range u.Entries {
			undelegationsInTokens = undelegationsInTokens.Add(entry.InitialBalance)
		}
	}

	// compute the total numbers of tokens currently being redelegated
	redelegationsInTokens := sdk.NewInt(0)
	for _, r := range redelegations {
		for _, entry := range r.Entries {
			redelegationsInTokens = redelegationsInTokens.Add(entry.InitialBalance)
		}
	}

	// The power we pass to staking's keeper `Slash` method is the current power of the validator together with the total
	// power of all the currently undelegated and redelegated tokens (see docs/docs/adrs/adr-013-equivocation-slashing.md).
	undelegationsAndRedelegationsInPower := sdk.TokensToConsensusPower(
		undelegationsInTokens.Add(redelegationsInTokens), powerReduction)

	return power + undelegationsAndRedelegationsInPower
}

// Slash validator based on the `providerAddr`
func (k Keeper) SlashValidator(ctx sdk.Context, providerAddr types.ProviderConsAddress) {
	logger := k.Logger(ctx)

	val, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, providerAddr.ToSdkConsAddr())
	if !found {
		logger.Error("validator not found", "provider consensus address", providerAddr.String())
		return
	}

	if k.slashingKeeper.IsTombstoned(ctx, providerAddr.ToSdkConsAddr()) {
		logger.Info("validator is already tombstoned", "provider consensus address", providerAddr.String())
		return
	}

	undelegations := k.stakingKeeper.GetUnbondingDelegationsFromValidator(ctx, val.GetOperator())
	redelegations := k.stakingKeeper.GetRedelegationsFromSrcValidator(ctx, val.GetOperator())
	lastPower := k.stakingKeeper.GetLastValidatorPower(ctx, val.GetOperator())
	powerReduction := k.stakingKeeper.PowerReduction(ctx)
	totalPower := k.ComputePowerToSlash(undelegations, redelegations, lastPower, powerReduction)

	slashFraction := k.slashingKeeper.SlashFractionDoubleSign(ctx)

	k.stakingKeeper.Slash(ctx, providerAddr.ToSdkConsAddr(), 0, totalPower, slashFraction, stakingtypes.DoubleSign)
}
