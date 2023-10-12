package keeper

import (
	"fmt"

	errorsmod "cosmossdk.io/errors"
	"cosmossdk.io/math"

	sdk "github.com/cosmos/cosmos-sdk/types"
	evidencetypes "github.com/cosmos/cosmos-sdk/x/evidence/types"
	slashingtypes "github.com/cosmos/cosmos-sdk/x/slashing/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	"github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
)

// JailAndTombstoneValidator jails and tombstones the validator with the given provider consensus address
func (k Keeper) JailAndTombstoneValidator(ctx sdk.Context, providerAddr types.ProviderConsAddress) error {
	validator, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, providerAddr.ToSdkConsAddr())
	if !found {
		return errorsmod.Wrapf(slashingtypes.ErrNoValidatorForAddress, "provider consensus address: %s", providerAddr.String())
	}

	if validator.IsUnbonded() {
		return fmt.Errorf("validator is unbonded. provider consensus address: %s", providerAddr.String())
	}

	if k.slashingKeeper.IsTombstoned(ctx, providerAddr.ToSdkConsAddr()) {
		return fmt.Errorf("validator is tombstoned. provider consensus address: %s", providerAddr.String())
	}

	// jail validator if not already
	if !validator.IsJailed() {
		k.stakingKeeper.Jail(ctx, providerAddr.ToSdkConsAddr())
	}

	// Jail the validator to trigger the unbonding of the validator
	// (see cosmos/cosmos-sdk/blob/v0.45.16-ics-lsm/x/staking/keeper/val_state_change.go#L192).
	k.slashingKeeper.JailUntil(ctx, providerAddr.ToSdkConsAddr(), evidencetypes.DoubleSignJailEndTime)

	// Tombstone the validator so that we cannot slash the validator more than once
	// Note that we cannot simply use the fact that a validator is jailed to avoid slashing more than once
	// because then a validator could i) perform an equivocation, ii) get jailed (e.g., through downtime)
	// and in such a case the validator would not get slashed when we call `SlashValidator`.
	k.slashingKeeper.Tombstone(ctx, providerAddr.ToSdkConsAddr())

	return nil
}

// ComputePowerToSlash computes the power to be slashed based on the tokens in non-matured `undelegations` and
// `redelegations`, as well as the current `power` of the validator.
// Note that this method does not perform any slashing.
func (k Keeper) ComputePowerToSlash(ctx sdk.Context, validator stakingtypes.Validator, undelegations []stakingtypes.UnbondingDelegation,
	redelegations []stakingtypes.Redelegation, power int64, powerReduction math.Int,
) int64 {
	// compute the total numbers of tokens currently being undelegated
	undelegationsInTokens := sdk.NewInt(0)

	// Note that we use a **cached** context to avoid any actual slashing of undelegations or redelegations.
	cachedCtx, _ := ctx.CacheContext()
	for _, u := range undelegations {
		amountSlashed := k.stakingKeeper.SlashUnbondingDelegation(cachedCtx, u, 0, sdk.NewDec(1))
		undelegationsInTokens = undelegationsInTokens.Add(amountSlashed)
	}

	// compute the total numbers of tokens currently being redelegated
	redelegationsInTokens := sdk.NewInt(0)
	for _, r := range redelegations {
		amountSlashed := k.stakingKeeper.SlashRedelegation(cachedCtx, validator, r, 0, sdk.NewDec(1))
		redelegationsInTokens = redelegationsInTokens.Add(amountSlashed)
	}

	// The power we pass to staking's keeper `Slash` method is the current power of the validator together with the total
	// power of all the currently undelegated and redelegated tokens (see docs/docs/adrs/adr-013-equivocation-slashing.md).
	undelegationsAndRedelegationsInPower := sdk.TokensToConsensusPower(
		undelegationsInTokens.Add(redelegationsInTokens), powerReduction)

	return power + undelegationsAndRedelegationsInPower
}

// SlashValidator slashes validator with `providerAddr`
func (k Keeper) SlashValidator(ctx sdk.Context, providerAddr types.ProviderConsAddress) error {
	validator, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, providerAddr.ToSdkConsAddr())
	if !found {
		return errorsmod.Wrapf(slashingtypes.ErrNoValidatorForAddress, "provider consensus address: %s", providerAddr.String())
	}

        // check if the validator is unbonded to prevent panicking when slashing (see cosmos/cosmos-sdk/blob/v0.47.5/x/staking/keeper/slash.go#L61)
	if validator.IsUnbonded() {
		return fmt.Errorf("validator is unbonded. provider consensus address: %s", providerAddr.String())
	}

        // check if the validator is already tombstoned to avoid slashing a validator more than once
	if k.slashingKeeper.IsTombstoned(ctx, providerAddr.ToSdkConsAddr()) {
		return fmt.Errorf("validator is tombstoned. provider consensus address: %s", providerAddr.String())
	}

	undelegations := k.stakingKeeper.GetUnbondingDelegationsFromValidator(ctx, validator.GetOperator())
	redelegations := k.stakingKeeper.GetRedelegationsFromSrcValidator(ctx, validator.GetOperator())
	lastPower := k.stakingKeeper.GetLastValidatorPower(ctx, validator.GetOperator())
	powerReduction := k.stakingKeeper.PowerReduction(ctx)
	totalPower := k.ComputePowerToSlash(ctx, validator, undelegations, redelegations, lastPower, powerReduction)
	slashFraction := k.slashingKeeper.SlashFractionDoubleSign(ctx)

	k.stakingKeeper.SlashWithInfractionReason(ctx, providerAddr.ToSdkConsAddr(), 0, totalPower, slashFraction, stakingtypes.Infraction_INFRACTION_DOUBLE_SIGN)
	return nil
}
