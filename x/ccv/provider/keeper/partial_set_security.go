package keeper

import (
	"fmt"
	"sort"

	errorsmod "cosmossdk.io/errors"
	"cosmossdk.io/math"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v5/x/ccv/types"
)

// HandleOptIn prepares validator `providerAddr` to opt in to `consumerId` with an optional `consumerKey` consumer public key.
// Note that the validator only opts in at the end of an epoch.
func (k Keeper) HandleOptIn(ctx sdk.Context, consumerId string, providerAddr types.ProviderConsAddress, consumerKey string) error {
	if !k.IsConsumerActive(ctx, consumerId) {
		return errorsmod.Wrapf(
			types.ErrInvalidPhase,
			"cannot opt in to a consumer chain that is not in the registered, initialized, or launched phase: %s", consumerId)
	}

	chainId, err := k.GetConsumerChainId(ctx, consumerId)
	if err != nil {
		// TODO (PERMISSIONLESS): fix error types
		return errorsmod.Wrapf(
			types.ErrUnknownConsumerId,
			"opting in to an unknown consumer chain, with id (%s): %s", consumerId, err.Error())
	}
	optedInToConsumerId, found := k.IsValidatorOptedInToChainId(ctx, providerAddr, chainId)
	if found {
		return errorsmod.Wrapf(types.ErrAlreadyOptedIn,
			"validator is already opted in to a chain (%s) with this chain id (%s)",
			optedInToConsumerId, chainId)
	}

	k.SetOptedIn(ctx, consumerId, providerAddr)
	err = k.AppendOptedInConsumerId(ctx, providerAddr, consumerId)
	if err != nil {
		return err
	}

	if consumerKey != "" {
		consumerTMPublicKey, err := k.ParseConsumerKey(consumerKey)
		if err != nil {
			return err
		}

		validator, err := k.stakingKeeper.GetValidatorByConsAddr(ctx, providerAddr.Address)
		if err != nil {
			return err
		}

		err = k.AssignConsumerKey(ctx, consumerId, validator, consumerTMPublicKey)
		if err != nil {
			return err
		}
	}

	return nil
}

// HandleOptOut prepares validator `providerAddr` to opt out from running `consumerId`.
// Note that the validator only opts out at the end of an epoch.
func (k Keeper) HandleOptOut(ctx sdk.Context, consumerId string, providerAddr types.ProviderConsAddress) error {
	phase := k.GetConsumerPhase(ctx, consumerId)
	if phase == types.CONSUMER_PHASE_UNSPECIFIED {
		return errorsmod.Wrapf(
			types.ErrUnknownConsumerId,
			"opting out of an unknown consumer chain, consumerId(%s)", consumerId,
		)
	}
	if phase != types.CONSUMER_PHASE_LAUNCHED {
		// A validator can only opt out from a running chain
		return errorsmod.Wrapf(
			types.ErrInvalidPhase,
			"opting out of a consumer chain not yet launched, consumerId(%s)", consumerId,
		)
	}

	powerShapingParameters, err := k.GetConsumerPowerShapingParameters(ctx, consumerId)
	if err != nil {
		return errorsmod.Wrapf(ccvtypes.ErrInvalidConsumerState,
			"cannot get consumer power shaping parameters: %s", err.Error(),
		)
	}
	if powerShapingParameters.Top_N > 0 {
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
		minPowerInTopN, found := k.GetMinimumPowerInTopN(ctx, consumerId)
		if !found {
			return errorsmod.Wrapf(
				types.ErrUnknownConsumerId,
				"Could not find minimum power in top N for chain with consumer id: %s", consumerId)
		}

		if power >= minPowerInTopN {
			return errorsmod.Wrapf(
				types.ErrCannotOptOutFromTopN,
				"validator with power (%d) cannot opt out from Top N chain with consumer id (%s) because all validators"+
					" with at least %d power have to validate", power, consumerId, minPowerInTopN)
		}
	}

	k.DeleteOptedIn(ctx, consumerId, providerAddr)
	return k.RemoveOptedInConsumerId(ctx, providerAddr, consumerId)
}

// OptInTopNValidators opts in to `consumerId` all the `bondedValidators` that have at least `minPowerToOptIn` power
func (k Keeper) OptInTopNValidators(ctx sdk.Context, consumerId string, bondedValidators []stakingtypes.Validator, minPowerToOptIn int64) {
	for _, val := range bondedValidators {
		// log the validator
		k.Logger(ctx).Debug("Checking whether to opt in validator because of top N", "validator", val.GetOperator())

		valAddr, err := sdk.ValAddressFromBech32(val.GetOperator())
		if err != nil {
			k.Logger(ctx).Error("could not retrieve validator address from operator address",
				"validator operator address", val.GetOperator(),
				"error", err.Error())
			continue
		}
		power, err := k.stakingKeeper.GetLastValidatorPower(ctx, valAddr)
		if err != nil {
			k.Logger(ctx).Error("could not retrieve last power of validator",
				"validator operator address", val.GetOperator(),
				"error", err.Error())
			continue
		}
		if power >= minPowerToOptIn {
			consAddr, err := val.GetConsAddr()
			if err != nil {
				k.Logger(ctx).Error("could not retrieve validator consensus address",
					"validator operator address", val.GetOperator(),
					"error", err.Error())
				continue
			}

			k.Logger(ctx).Debug("Opting in validator", "validator", val.GetOperator())

			// if validator already exists it gets overwritten
			err = k.AppendOptedInConsumerId(ctx, types.NewProviderConsAddress(consAddr), consumerId)
			if err != nil {
				k.Logger(ctx).Error("could not append validator as opted-in validator for this consumer chain",
					"validator operator address", val.GetOperator(),
					"consumer id", consumerId,
					"error", err.Error())
				continue
			}
			k.SetOptedIn(ctx, consumerId, types.NewProviderConsAddress(consAddr))
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

// CapValidatorSet caps the provided `validators` if chain with `consumerId` is an Opt In chain with a validator-set cap.
// If cap is `k`, `CapValidatorSet` returns the first `k` validators from `validators` with the highest power.
func (k Keeper) CapValidatorSet(
	ctx sdk.Context,
	powerShapingParameters types.PowerShapingParameters,
	validators []types.ConsensusValidator,
) []types.ConsensusValidator {
	if powerShapingParameters.Top_N > 0 {
		// is a no-op if the chain is a Top N chain
		return validators
	}

	validatorSetCap := powerShapingParameters.ValidatorSetCap
	if validatorSetCap != 0 && int(validatorSetCap) < len(validators) {
		sort.Slice(validators, func(i, j int) bool {
			return validators[i].Power > validators[j].Power
		})

		return validators[:int(validatorSetCap)]
	} else {
		return validators
	}
}

// CapValidatorsPower caps the power of the validators on chain with `consumerId` and returns an updated slice of validators
// with their new powers. Works on a best-basis effort because there are cases where we cannot guarantee that all validators
// on the consumer chain have less power than the set validators-power cap. For example, if we have 10 validators and
// the power cap is set to 5%, we need at least one validator to have more than 10% of the voting power on the consumer chain.
func (k Keeper) CapValidatorsPower(
	ctx sdk.Context,
	validatorsPowerCap uint32,
	validators []types.ConsensusValidator,
) []types.ConsensusValidator {
	if validatorsPowerCap > 0 {
		return NoMoreThanPercentOfTheSum(validators, validatorsPowerCap)
	} else {
		// is a no-op if power cap is not set for `consumerId`
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

// CanValidateChain returns true if the validator `providerAddr` is opted-in to chain with `consumerId` and the allowlist
// and denylist do not prevent the validator from validating the chain.
func (k Keeper) CanValidateChain(
	ctx sdk.Context,
	consumerId string,
	providerAddr types.ProviderConsAddress,
	topN uint32,
	minPowerToOptIn int64,
) bool {
	// check if the validator is already opted-in
	optedIn := k.IsOptedIn(ctx, consumerId, providerAddr)

	// check if the validator is automatically opted-in for a topN chain
	if !optedIn && topN > 0 {
		optedIn = k.HasMinPower(ctx, providerAddr, minPowerToOptIn)
	}

	// only consider opted-in validators
	return optedIn &&
		// if an allowlist is declared, only consider allowlisted validators
		(k.IsAllowlistEmpty(ctx, consumerId) ||
			k.IsAllowlisted(ctx, consumerId, providerAddr)) &&
		// if a denylist is declared, only consider denylisted validators
		(k.IsDenylistEmpty(ctx, consumerId) ||
			!k.IsDenylisted(ctx, consumerId, providerAddr))
}

// FulfillsMinStake returns true if the validator `providerAddr` has enough stake to validate chain with `consumerId`
// by checking its staked tokens against the minimum stake required to validate the chain.
func (k Keeper) FulfillsMinStake(
	ctx sdk.Context,
	minStake uint64,
	providerAddr types.ProviderConsAddress,
) bool {
	if minStake == 0 {
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
func (k Keeper) ComputeNextValidators(
	ctx sdk.Context,
	consumerId string,
	bondedValidators []stakingtypes.Validator,
	powerShapingParameters types.PowerShapingParameters,
	minPowerToOptIn int64,
) []types.ConsensusValidator {
	// sort the bonded validators by number of staked tokens in descending order
	sort.Slice(bondedValidators, func(i, j int) bool {
		return bondedValidators[i].GetBondedTokens().GT(bondedValidators[j].GetBondedTokens())
	})

	// if inactive validators are not allowed, only consider the first `MaxProviderConsensusValidators` validators
	// since those are the ones that participate in consensus
	if !powerShapingParameters.AllowInactiveVals {
		// only leave the first MaxProviderConsensusValidators bonded validators
		maxProviderConsensusVals := k.GetMaxProviderConsensusValidators(ctx)
		if len(bondedValidators) > int(maxProviderConsensusVals) {
			bondedValidators = bondedValidators[:maxProviderConsensusVals]
		}
	}

	nextValidators := k.FilterValidators(ctx, consumerId, bondedValidators,
		func(providerAddr types.ProviderConsAddress) bool {
			return k.CanValidateChain(ctx, consumerId, providerAddr, powerShapingParameters.Top_N, minPowerToOptIn) &&
				k.FulfillsMinStake(ctx, powerShapingParameters.MinStake, providerAddr)
		})

	nextValidators = k.CapValidatorSet(ctx, powerShapingParameters, nextValidators)
	return k.CapValidatorsPower(ctx, powerShapingParameters.ValidatorsPowerCap, nextValidators)
}

// HasMinPower returns true if the `providerAddr` voting power is GTE than the given minimum power
func (k Keeper) HasMinPower(ctx sdk.Context, providerAddr types.ProviderConsAddress, minPower int64) bool {
	val, err := k.stakingKeeper.GetValidatorByConsAddr(ctx, providerAddr.Address)
	if err != nil {
		k.Logger(ctx).Error(
			"cannot get last validator power",
			"provider address",
			providerAddr,
			"error",
			err,
		)
		return false
	}

	valAddr, err := sdk.ValAddressFromBech32(val.GetOperator())
	if err != nil {
		k.Logger(ctx).Error(
			"could not retrieve validator address",
			"operator address",
			val.GetOperator(),
			"error",
			err,
		)
		return false
	}

	power, err := k.stakingKeeper.GetLastValidatorPower(ctx, valAddr)
	if err != nil {
		k.Logger(ctx).Error("could not retrieve last power of validator address",
			"operator address",
			val.GetOperator(),
			"error",
			err,
		)
		return false
	}

	return power >= minPower
}
