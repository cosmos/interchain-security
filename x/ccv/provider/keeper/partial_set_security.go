package keeper

import (
	"math"
	"sort"

	errorsmod "cosmossdk.io/errors"
	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	"github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
)

// HandleOptIn prepares validator `providerAddr` to opt in to `chainID` with an optional `consumerKey` consumer public key.
// Note that the validator only opts in at the end of an epoch.
func (k Keeper) HandleOptIn(ctx sdk.Context, chainID string, providerAddr types.ProviderConsAddress, consumerKey *string) error {
	if !k.IsConsumerProposedOrRegistered(ctx, chainID) {
		return errorsmod.Wrapf(
			types.ErrUnknownConsumerChainId,
			"opting in to an unknown consumer chain, with id: %s", chainID)
	}

	k.SetOptedIn(ctx, chainID, providerAddr)

	if consumerKey != nil {
		consumerTMPublicKey, err := k.ParseConsumerKey(*consumerKey)
		if err != nil {
			return err
		}

		validator, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, providerAddr.Address)
		if !found {
			return stakingtypes.ErrNoValidatorFound
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
		validator, validatorFound := k.stakingKeeper.GetValidatorByConsAddr(ctx, providerAddr.ToSdkConsAddr())
		if !validatorFound {
			return errorsmod.Wrapf(
				stakingtypes.ErrNoValidatorFound,
				"validator with consensus address %s could not be found", providerAddr.ToSdkConsAddr())
		}
		power := k.stakingKeeper.GetLastValidatorPower(ctx, validator.GetOperator())
		minPowerToOptIn := k.ComputeMinPowerToOptIn(ctx, chainID, k.stakingKeeper.GetLastValidators(ctx), topN)

		if power >= minPowerToOptIn {
			return errorsmod.Wrapf(
				types.ErrCannotOptOutFromTopN,
				"validator with power (%d) cannot opt out from Top N chain because all validators"+
					"with at least %d power have to validate", power, minPowerToOptIn)
		}
	}

	k.DeleteOptedIn(ctx, chainID, providerAddr)
	return nil
}

// OptInTopNValidators opts in to `chainID` all the `bondedValidators` that have at least `minPowerToOptIn` power
func (k Keeper) OptInTopNValidators(ctx sdk.Context, chainID string, bondedValidators []stakingtypes.Validator, minPowerToOptIn int64) {
	for _, val := range bondedValidators {
		power := k.stakingKeeper.GetLastValidatorPower(ctx, val.GetOperator())
		if power >= minPowerToOptIn {
			consAddr, err := val.GetConsAddr()
			if err != nil {
				k.Logger(ctx).Error("could not retrieve validators consensus address",
					"validator", val,
					"error", err)
				continue
			}

			// if validator already exists it gets overwritten
			k.SetOptedIn(ctx, chainID, types.NewProviderConsAddress(consAddr))
		} // else validators that do not belong to the top N validators but were opted in, remain opted in
	}
}

// ComputeMinPowerToOptIn returns the minimum power needed for a validator (from the bonded validators)
// to belong to the `topN` validators. `chainID` is only used for logging purposes.
func (k Keeper) ComputeMinPowerToOptIn(ctx sdk.Context, chainID string, bondedValidators []stakingtypes.Validator, topN uint32) int64 {
	if topN == 0 {
		// This should never happen but because `ComputeMinPowerToOptIn` is called during an `EndBlock` we do want
		// to `panic` here. Instead, we log an error and return the maximum possible `int64`.
		k.Logger(ctx).Error("trying to compute minimum power to opt in for a non-Top-N chain",
			"chainID", chainID)
		return math.MaxInt64
	}

	totalPower := sdk.ZeroDec()
	var powers []int64

	for _, val := range bondedValidators {
		power := k.stakingKeeper.GetLastValidatorPower(ctx, val.GetOperator())
		powers = append(powers, power)
		totalPower = totalPower.Add(sdk.NewDecFromInt(sdk.NewInt(power)))
	}

	// sort by powers descending
	sort.Slice(powers, func(i, j int) bool {
		return powers[i] > powers[j]
	})

	topNThreshold := sdk.NewDecFromInt(sdk.NewInt(int64(topN))).QuoInt64(int64(100))
	powerSum := sdk.ZeroDec()
	for _, power := range powers {
		powerSum = powerSum.Add(sdk.NewDecFromInt(sdk.NewInt(power)))
		if powerSum.Quo(totalPower).GTE(topNThreshold) {
			return power
		}
	}

	// We should never reach this point because the topN can be up to 1.0 (100%) and in the above `for` loop we
	// perform an equal comparison as well (`GTE`). In any case, we do not have to panic here because we can return 0
	// as the smallest possible power.
	k.Logger(ctx).Error("should never reach this point",
		"topN", topN,
		"totalPower", totalPower,
		"powerSum", powerSum)
	return 0
}

// CapValidatorSet caps the provided `validators` if chain `chainID` is an Opt In chain with a validator-set cap. If cap
// is `k`, `CapValidatorSet` returns the first `k` validators from `validators` with the highest power.
func (k Keeper) CapValidatorSet(ctx sdk.Context, chainID string, validators []types.ConsumerValidator) []types.ConsumerValidator {
	if topN, found := k.GetTopN(ctx, chainID); found && topN > 0 {
		// is a no-op if the chain is a Top N chain
		return validators
	}

	if validatorSetCap, found := k.GetValidatorSetCap(ctx, chainID); found && validatorSetCap != 0 {
		sort.Slice(validators, func(i, j int) bool {
			return validators[i].Power > validators[j].Power
		})

		minNumberOfValidators := 0
		if len(validators) < int(validatorSetCap) {
			minNumberOfValidators = len(validators)
		} else {
			minNumberOfValidators = int(validatorSetCap)
		}
		return validators[:minNumberOfValidators]
	} else {
		return validators
	}
}

// CapValidatorsPower caps the power of the validators on chain `chainID` and returns an updated slice of validators
// with their new powers. Works on a best-basis effort because there are cases where we cannot guarantee that all validators
// on the consumer chain have less power than the set validators-power cap. For example, if we have 10 validators and
// the power cap is set to 5%, we need at least one validator to have more than 10% of the voting power on the consumer chain.
func (k Keeper) CapValidatorsPower(ctx sdk.Context, chainID string, validators []types.ConsumerValidator) []types.ConsumerValidator {
	if p, found := k.GetValidatorsPowerCap(ctx, chainID); found {
		return NoMoreThanPercentOfTheSum(validators, p)
	} else {
		// is a no-op if power cap is not set for `chainID`
		return validators
	}
}

// sum is a helper function to sum all the validators' power
func sum(validators []types.ConsumerValidator) int64 {
	s := int64(0)
	for _, v := range validators {
		s = s + v.Power
	}
	return s
}

// NoMoreThanPercentOfTheSum returns a set of validators with updated powers such that no validator has more than the
// provided `percent` of the sum of all validators' powers.
func NoMoreThanPercentOfTheSum(validators []types.ConsumerValidator, percent uint32) []types.ConsumerValidator {
	// The idea behind this algorithm is rather simple:
	// - Compute the `maxPower` a validator must have so that it does not have more than `percent` of the voting power.
	// - If a validator `v` has power `p`, then:
	//     - if `p > maxPower` we set `v`'s power to `maxPower` and distribute the `p - maxPower` to validators that
	//       have less than `maxPower` power
	s := sum(validators)
	maxPower := int64(float64(s) * (float64(percent) / 100.0))
	if maxPower == 0 {
		// edge case: set `maxPower` to 1 to avoid setting the power of a validator to 0
		maxPower = 1
	}

	// Sort by `.Power` in decreasing order. This way, we improve the chances that if a validator `a` has more power
	// than a validator `b` in `validators`, `a` has still more than `b` in the return validators.
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

	updatedValidators := make([]types.ConsumerValidator, len(validators))

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

// FilterOptedInAndAllowAndDenylistedPredicate filters the opted-in validators that are allowlisted and not denylisted
func (k Keeper) FilterOptedInAndAllowAndDenylistedPredicate(ctx sdk.Context, chainID string, providerAddr types.ProviderConsAddress) bool {
	// only consider opted-in validators
	return k.IsOptedIn(ctx, chainID, providerAddr) &&
		// if an allowlist is declared, only consider allowlisted validators
		(k.IsAllowlistEmpty(ctx, chainID) ||
			k.IsAllowlisted(ctx, chainID, providerAddr)) &&
		// if a denylist is declared, only consider denylisted validators
		(k.IsDenylistEmpty(ctx, chainID) ||
			!k.IsDenylisted(ctx, chainID, providerAddr))
}
