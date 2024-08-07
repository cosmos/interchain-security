package keeper

import (
	"fmt"
	"sort"

	errorsmod "cosmossdk.io/errors"
	"cosmossdk.io/math"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
)

// HandleOptIn prepares validator `providerAddr` to opt in to `chainID` with an optional `consumerKey` consumer public key.
// Note that the validator only opts in at the end of an epoch.
func (k Keeper) HandleOptIn(ctx sdk.Context, chainID string, providerAddr types.ProviderConsAddress, consumerKey string) error {
	if !k.IsConsumerProposedOrRegistered(ctx, chainID) {
		return errorsmod.Wrapf(
			types.ErrUnknownConsumerChainId,
			"opting in to an unknown consumer chain, with id: %s", chainID)
	}

	k.SetOptedIn(ctx, chainID, providerAddr)

	if consumerKey != "" {
		consumerTMPublicKey, err := k.ParseConsumerKey(consumerKey)
		if err != nil {
			return err
		}

		validator, err := k.stakingKeeper.GetValidatorByConsAddr(ctx, providerAddr.Address)
		if err != nil {
			return err
		}

		err = k.AssignConsumerKey(ctx, chainID, validator, consumerTMPublicKey)
		if err != nil {
			return err
		}
	}

	return nil
}

// HandleOptOut prepares validator `providerAddr` to opt out from running `chainID`.
// Note that the validator only opts out at the end of an epoch.
func (k Keeper) HandleOptOut(ctx sdk.Context, chainID string, providerAddr types.ProviderConsAddress) error {
	if _, found := k.GetConsumerClientId(ctx, chainID); !found {
		// A validator can only opt out from a running chain. We check this by checking the consumer client id, because
		// `SetConsumerClientId` is set when the chain starts in `CreateConsumerClientInCachedCtx` of `BeginBlockInit`.
		return errorsmod.Wrapf(
			types.ErrUnknownConsumerChainId,
			"opting out of an unknown or not running consumer chain, with id: %s", chainID)
	}

	if topN, found := k.GetTopN(ctx, chainID); found && topN > 0 {
		// a validator cannot opt out from a Top N chain if the validator is in the Top N validators
		validator, err := k.stakingKeeper.GetValidatorByConsAddr(ctx, providerAddr.ToSdkConsAddr())
		if err != nil {
			return err
		}
		valAddr, err := sdk.ValAddressFromBech32(validator.GetOperator())
		if err != nil {
			return err
		}
		power, err := k.stakingKeeper.GetLastValidatorPower(ctx, valAddr)
		if err != nil {
			return err
		}
		minPowerInTopN, found := k.GetMinimumPowerInTopN(ctx, chainID)
		if !found {
			return errorsmod.Wrapf(
				types.ErrUnknownConsumerChainId,
				"Could not find minimum power in top N for chain with id: %s", chainID)
		}

		if power >= minPowerInTopN {
			return errorsmod.Wrapf(
				types.ErrCannotOptOutFromTopN,
				"validator with power (%d) cannot opt out from Top N chain (%s) because all validators"+
					" with at least %d power have to validate", power, chainID, minPowerInTopN)
		}
	}

	k.DeleteOptedIn(ctx, chainID, providerAddr)
	return nil
}

// OptInTopNValidators opts in to `chainID` all the `bondedValidators` that have at least `minPowerToOptIn` power
func (k Keeper) OptInTopNValidators(ctx sdk.Context, chainID string, bondedValidators []stakingtypes.Validator, minPowerToOptIn int64) {
	for _, val := range bondedValidators {
		valAddr, err := sdk.ValAddressFromBech32(val.GetOperator())
		if err != nil {
			k.Logger(ctx).Error("could not retrieve validator address: %s: %s",
				val.GetOperator(), err)
			continue
		}
		power, err := k.stakingKeeper.GetLastValidatorPower(ctx, valAddr)
		if err != nil {
			k.Logger(ctx).Error("could not retrieve last power of validator address: %s: %s",
				val.GetOperator(), err)
			continue
		}
		if power >= minPowerToOptIn {
			consAddr, err := val.GetConsAddr()
			if err != nil {
				k.Logger(ctx).Error("could not retrieve validators consensus address: %s: %s",
					val, err)
				continue
			}

			// if validator already exists it gets overwritten
			k.SetOptedIn(ctx, chainID, types.NewProviderConsAddress(consAddr))
		} // else validators that do not belong to the top N validators but were opted in, remain opted in
	}
}

// ComputeMinPowerInTopN returns the minimum power needed for a validator (from the bonded validators)
// to belong to the `topN`% of validators for a Top N chain.
func (k Keeper) ComputeMinPowerInTopN(ctx sdk.Context, bondedValidators []stakingtypes.Validator, topN uint32) (int64, error) {
	if topN == 0 || topN > 100 {
		// Note that Top N chains have a lower limit on `topN`, namely that topN cannot be less than 50.
		// However, we can envision that this method could be used for other (future) reasons where this might not
		// be the case. For this, this method operates for `topN`s in (0, 100].
		return 0, fmt.Errorf("trying to compute minimum power with an incorrect"+
			" topN value (%d). topN has to be in (0, 100]", topN)
	}

	totalPower := math.LegacyZeroDec()
	var powers []int64

	for _, val := range bondedValidators {
		valAddr, err := sdk.ValAddressFromBech32(val.GetOperator())
		if err != nil {
			return 0, err
		}
		power, err := k.stakingKeeper.GetLastValidatorPower(ctx, valAddr)
		if err != nil {
			return 0, err
		}
		powers = append(powers, power)
		totalPower = totalPower.Add(math.LegacyNewDec(power))
	}

	// sort by powers descending
	sort.Slice(powers, func(i, j int) bool {
		return powers[i] > powers[j]
	})

	topNThreshold := math.LegacyNewDec(int64(topN)).QuoInt64(int64(100))
	powerSum := math.LegacyZeroDec()
	for _, power := range powers {
		powerSum = powerSum.Add(math.LegacyNewDec(power))
		if powerSum.Quo(totalPower).GTE(topNThreshold) {
			return power, nil
		}
	}

	// We should never reach this point because the topN can be up to 1.0 (100%) and in the above `for` loop we
	// perform an equal comparison as well (`GTE`).
	return 0, fmt.Errorf("should never reach this point with topN (%d), totalPower (%d), and powerSum (%d)", topN, totalPower, powerSum)
}

// CapValidatorSet caps the provided `validators` if chain `chainID` is an Opt In chain with a validator-set cap. If cap
// is `k`, `CapValidatorSet` returns the first `k` validators from `validators` with the highest power.
func (k Keeper) CapValidatorSet(ctx sdk.Context, chainID string, validators []types.ConsensusValidator) []types.ConsensusValidator {
	if topN, found := k.GetTopN(ctx, chainID); found && topN > 0 {
		// is a no-op if the chain is a Top N chain
		return validators
	}

	if validatorSetCap, found := k.GetValidatorSetCap(ctx, chainID); found && validatorSetCap != 0 && int(validatorSetCap) < len(validators) {
		sort.Slice(validators, func(i, j int) bool {
			return validators[i].Power > validators[j].Power
		})

		return validators[:int(validatorSetCap)]
	} else {
		return validators
	}
}

// CapValidatorsPower caps the power of the validators on chain `chainID` and returns an updated slice of validators
// with their new powers. Works on a best-basis effort because there are cases where we cannot guarantee that all validators
// on the consumer chain have less power than the set validators-power cap. For example, if we have 10 validators and
// the power cap is set to 5%, we need at least one validator to have more than 10% of the voting power on the consumer chain.
func (k Keeper) CapValidatorsPower(ctx sdk.Context, chainID string, validators []types.ConsensusValidator) []types.ConsensusValidator {
	if p, found := k.GetValidatorsPowerCap(ctx, chainID); found && p > 0 {
		return NoMoreThanPercentOfTheSum(validators, p)
	} else {
		// is a no-op if power cap is not set for `chainID`
		return validators
	}
}

// sum is a helper function to sum all the validators' power
func sum(validators []types.ConsensusValidator) int64 {
	s := int64(0)
	for _, v := range validators {
		s = s + v.Power
	}
	return s
}

// NoMoreThanPercentOfTheSum returns a set of validators with updated powers such that no validator has more than the
// provided `percent` of the sum of all validators' powers. Operates on a best-effort basis.
func NoMoreThanPercentOfTheSum(validators []types.ConsensusValidator, percent uint32) []types.ConsensusValidator {
	// Algorithm's idea
	// ----------------
	// Consider the validators' powers to be `a_1, a_2, ... a_n` and `p` to be the percent in [1, 100]. Now, consider
	// the sum `s = a_1 + a_2 + ... + a_n`. Then `maxPower = s * p / 100 <=> 100 * maxPower = s * p`.
	// The problem of capping the validators' powers to be no more than `p` has no solution if `(100 / n) > p`. For example,
	// for n = 10 and p = 5 we do not have a solution. We would need at least one validator with power greater than 10%
	// for a solution to exist.
	// So, if `(100 / n) > p` there's no solution. We know that `100 * maxPower = s * p` and so `(100 / n) > (100 * maxPower) / s`
	// `100 * s > 100 * maxPower * n <=> s > maxPower * n`. Thus, we do not have a solution if `s > n * maxPower`.

	// If `s <= n * maxPower` the idea of the algorithm is rather simple.
	// - Compute the `maxPower` a validator must have so that it does not have more than `percent` of the voting power.
	// - If a validator `v` has power `p`, then:
	//     - if `p > maxPower` we set `v`'s power to `maxPower` and distribute the `p - maxPower` to validators that
	//       have less than `maxPower` power. This way, the total sum remains the same and no validator has more than
	//       `maxPower` and so the power capping is satisfied.
	// - Note that in order to avoid setting multiple validators to `maxPower`, we first compute all the `remainingPower`
	// we have to distribute and then attempt to add `remainingPower / validatorsWithPowerLessThanMaxPower` to each validator.
	// To guarantee that the sum remains the same after the distribution of powers, we sort the powers in descending
	// order. This way, we first attempt to add `remainingPower / validatorsWithPowerLessThanMaxPower` to validators
	// with greater power and if we cannot add the `remainingPower / validatorsWithPowerLessThanMaxPower` without
	// exceeding `maxPower`, we just add enough to reach `maxPower` and add the remaining power to validators with smaller
	// power.

	// If `s > n * maxPower` there's no solution and the algorithm would set everything to `maxPower`.
	// ----------------

	// Computes `floor((sum(validators) * percent) / 100)`
	maxPower := math.LegacyNewDec(sum(validators)).Mul(math.LegacyNewDec(int64(percent))).QuoInt64(100).TruncateInt64()

	if maxPower == 0 {
		// edge case: set `maxPower` to 1 to avoid setting the power of a validator to 0
		maxPower = 1
	}

	// Sort by `.Power` in decreasing order. Sorting in descending order is needed because otherwise we would have cases
	// like this `powers =[60, 138, 559]` and `p = 35%` where sum is `757` and `maxValue = 264`.
	// Because `559 - 264 = 295` we have to distribute 295 to the first 2 numbers (`295/2 = 147` to each number). However,
	// note that `138 + 147 > 264`. If we were to add 147 to 60 first, then we cannot give the remaining 147 to 138.
	// So, the idea is to first give `126 (= 264 - 138)` to 138, so it becomes 264, and then add `21 (=147 - 26) + 147` to 60.
	sort.Slice(validators, func(i, j int) bool {
		return validators[i].Power > validators[j].Power
	})

	// `remainingPower` is to be distributed to validators that have power less than `maxPower`
	remainingPower := int64(0)
	validatorsWithPowerLessThanMaxPower := 0
	for _, v := range validators {
		if v.Power >= maxPower {
			remainingPower = remainingPower + (v.Power - maxPower)
		} else {
			validatorsWithPowerLessThanMaxPower++
		}
	}

	updatedValidators := make([]types.ConsensusValidator, len(validators))

	powerPerValidator := int64(0)
	remainingValidators := int64(validatorsWithPowerLessThanMaxPower)
	if remainingValidators != 0 {
		// power to give to each validator in order to distribute the `remainingPower`
		powerPerValidator = remainingPower / remainingValidators
	}

	for i, v := range validators {
		if v.Power >= maxPower {
			updatedValidators[i] = validators[i]
			updatedValidators[i].Power = maxPower
		} else if v.Power+powerPerValidator >= maxPower {
			updatedValidators[i] = validators[i]
			updatedValidators[i].Power = maxPower
			remainingPower = remainingPower - (maxPower - v.Power)
			remainingValidators--
		} else {
			updatedValidators[i] = validators[i]
			updatedValidators[i].Power = v.Power + powerPerValidator
			remainingPower = remainingPower - (updatedValidators[i].Power - validators[i].Power)
			remainingValidators--
		}
		if remainingValidators == 0 {
			continue
		}
		powerPerValidator = remainingPower / remainingValidators
	}

	return updatedValidators
}

// CanValidateChain returns true if the validator `providerAddr` is opted-in to chain `chainID` and the allowlist and
// denylist do not prevent the validator from validating the chain.
func (k Keeper) CanValidateChain(ctx sdk.Context, chainID string, providerAddr types.ProviderConsAddress) bool {
	// only consider opted-in validators
	return k.IsOptedIn(ctx, chainID, providerAddr) &&
		// if an allowlist is declared, only consider allowlisted validators
		(k.IsAllowlistEmpty(ctx, chainID) ||
			k.IsAllowlisted(ctx, chainID, providerAddr)) &&
		// if a denylist is declared, only consider denylisted validators
		(k.IsDenylistEmpty(ctx, chainID) ||
			!k.IsDenylisted(ctx, chainID, providerAddr))
}

// FulfillsMinStake returns true if the validator `providerAddr` has enough stake to validate chain `chainID`
// by checking its staked tokens against the minimum stake required to validate the chain.
func (k Keeper) FulfillsMinStake(ctx sdk.Context, chainID string, providerAddr types.ProviderConsAddress) bool {
	minStake, found := k.GetMinStake(ctx, chainID)
	if !found {
		return true
	}

	validator, err := k.stakingKeeper.GetValidatorByConsAddr(ctx, providerAddr.Address)
	if err != nil {
		k.Logger(ctx).Error("could not retrieve validator by consensus address", "consensus address", providerAddr, "error", err)
		return false
	}

	// validator has enough stake to validate the chain
	return validator.GetBondedTokens().GTE(math.NewIntFromUint64(minStake))
}

// ComputeNextValidators computes the validators for the upcoming epoch based on the currently `bondedValidators`.
func (k Keeper) ComputeNextValidators(ctx sdk.Context, chainID string, bondedValidators []stakingtypes.Validator) []types.ConsensusValidator {
	// sort the bonded validators by number of staked tokens in descending order
	sort.Slice(bondedValidators, func(i, j int) bool {
		return bondedValidators[i].GetBondedTokens().GT(bondedValidators[j].GetBondedTokens())
	})

	// if inactive validators are not allowed, only consider the first `MaxProviderConsensusValidators` validators
	// since those are the ones that participate in consensus
	allowInactiveVals := k.AllowsInactiveValidators(ctx, chainID)
	if !allowInactiveVals {
		// only leave the first MaxProviderConsensusValidators bonded validators
		maxProviderConsensusVals := k.GetMaxProviderConsensusValidators(ctx)
		if len(bondedValidators) > int(maxProviderConsensusVals) {
			bondedValidators = bondedValidators[:maxProviderConsensusVals]
		}
	}

	nextValidators := k.FilterValidators(ctx, chainID, bondedValidators,
		func(providerAddr types.ProviderConsAddress) bool {
			return k.CanValidateChain(ctx, chainID, providerAddr) && k.FulfillsMinStake(ctx, chainID, providerAddr)
		})

	nextValidators = k.CapValidatorSet(ctx, chainID, nextValidators)
	return k.CapValidatorsPower(ctx, chainID, nextValidators)
}
