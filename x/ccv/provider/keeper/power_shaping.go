package keeper

import (
	"encoding/binary"
	"errors"
	"fmt"
	"slices"
	"sort"

	errorsmod "cosmossdk.io/errors"
	"cosmossdk.io/math"
	storetypes "cosmossdk.io/store/types"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	"github.com/cosmos/interchain-security/v7/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v7/x/ccv/types"
)

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

// UpdateMinimumPowerInTopN populates the minimum power in Top N for the consumer chain with this consumer id
func (k Keeper) UpdateMinimumPowerInTopN(ctx sdk.Context, consumerId string, oldTopN, newTopN uint32) error {
	// if the top N changes, we need to update the new minimum power in top N
	if newTopN != oldTopN {
		if newTopN > 0 {
			// if the chain receives a non-zero top N value, store the minimum power in the top N
			bondedValidators, err := k.GetLastProviderConsensusActiveValidators(ctx)
			if err != nil {
				return err
			}
			minPower, err := k.ComputeMinPowerInTopN(ctx, bondedValidators, newTopN)
			if err != nil {
				return err
			}
			k.SetMinimumPowerInTopN(ctx, consumerId, minPower)
		} else {
			// if the chain receives a zero top N value, we delete the min power
			k.DeleteMinimumPowerInTopN(ctx, consumerId)
		}
	}

	return nil
}

// CapValidatorSet caps the provided `validators` if chain with `consumerId` is an Opt In chain with a validator-set cap.
// If cap is `k`, `CapValidatorSet` returns the first `k` validators from `validators`.
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
		// validators are already sorted by priority and power
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
		s += v.Power
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
			remainingPower += (v.Power - maxPower)
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
			remainingPower -= (maxPower - v.Power)
			remainingValidators--
		} else {
			updatedValidators[i] = validators[i]
			updatedValidators[i].Power = v.Power + powerPerValidator
			remainingPower -= (updatedValidators[i].Power - validators[i].Power)
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
) (bool, error) {
	// check if the validator is already opted-in
	optedIn := k.IsOptedIn(ctx, consumerId, providerAddr)

	// check if the validator is automatically opted-in for a topN chain
	if !optedIn && topN > 0 {
		var err error
		optedIn, err = k.HasMinPower(ctx, providerAddr, minPowerToOptIn)
		if err != nil {
			return false, err
		}
	}

	// only consider opted-in validators
	return optedIn &&
		// if an allowlist is declared, only consider allowlisted validators
		(k.IsAllowlistEmpty(ctx, consumerId) ||
			k.IsAllowlisted(ctx, consumerId, providerAddr)) &&
		// if a denylist is declared, only consider denylisted validators
		(k.IsDenylistEmpty(ctx, consumerId) ||
			!k.IsDenylisted(ctx, consumerId, providerAddr)), nil
}

// FulfillsMinStake returns true if the validator `providerAddr` has enough stake to validate chain with `consumerId`
// by checking its staked tokens against the minimum stake required to validate the chain.
func (k Keeper) FulfillsMinStake(
	ctx sdk.Context,
	minStake uint64,
	providerAddr types.ProviderConsAddress,
) (bool, error) {
	if minStake == 0 {
		return true, nil
	}

	validator, err := k.stakingKeeper.GetValidatorByConsAddr(ctx, providerAddr.Address)
	if err != nil {
		return false, err
	}

	// validator has enough stake to validate the chain
	return validator.GetBondedTokens().GTE(math.NewIntFromUint64(minStake)), nil
}

// HasMinPower returns true if the `providerAddr` voting power is GTE than the given minimum power
func (k Keeper) HasMinPower(ctx sdk.Context, providerAddr types.ProviderConsAddress, minPower int64) (bool, error) {
	val, err := k.stakingKeeper.GetValidatorByConsAddr(ctx, providerAddr.Address)
	if err != nil {
		return false, err
	}

	valAddr, err := sdk.ValAddressFromBech32(val.GetOperator())
	if err != nil {
		return false, err
	}

	power, err := k.stakingKeeper.GetLastValidatorPower(ctx, valAddr)
	if err != nil {
		return false, err
	}

	return power >= minPower, nil
}

//
// Setter and getters
//

// GetConsumerPowerShapingParameters returns the power-shaping parameters associated with this consumer id
func (k Keeper) GetConsumerPowerShapingParameters(ctx sdk.Context, consumerId string) (types.PowerShapingParameters, error) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerIdToPowerShapingParametersKey(consumerId))
	if bz == nil {
		return types.PowerShapingParameters{}, errorsmod.Wrapf(ccvtypes.ErrStoreKeyNotFound,
			"GetConsumerPowerShapingParameters, consumerId(%s)", consumerId)
	}
	var parameters types.PowerShapingParameters
	if err := parameters.Unmarshal(bz); err != nil {
		return types.PowerShapingParameters{}, errorsmod.Wrapf(ccvtypes.ErrStoreUnmarshal,
			"GetConsumerPowerShapingParameters, consumerId(%s): %s", consumerId, err.Error())
	}
	return parameters, nil
}

// SetConsumerPowerShapingParameters sets the power-shaping parameters associated with this consumer id.
// Note that it also updates the allowlist and denylist indexes if they are different
func (k Keeper) SetConsumerPowerShapingParameters(ctx sdk.Context, consumerId string, parameters types.PowerShapingParameters) error {
	store := ctx.KVStore(k.storeKey)
	bz, err := parameters.Marshal()
	if err != nil {
		return fmt.Errorf("failed to marshal power-shaping parameters (%+v) for consumer id (%s): %w", parameters, consumerId, err)
	}

	// get old power shaping params
	oldParameters, err := k.GetConsumerPowerShapingParameters(ctx, consumerId)
	// ignore ErrStoreKeyNotFound errors as this might be the first time the power shaping params are set
	if errors.Is(err, ccvtypes.ErrStoreUnmarshal) {
		return fmt.Errorf("cannot get consumer previous power shaping parameters: %w", err)
	}

	store.Set(types.ConsumerIdToPowerShapingParametersKey(consumerId), bz)

	// update allowlist, denylist and prioritylist indexes if needed
	if !slices.Equal(oldParameters.Allowlist, parameters.Allowlist) {
		k.UpdateAllowlist(ctx, consumerId, parameters.Allowlist)
	}
	if !slices.Equal(oldParameters.Denylist, parameters.Denylist) {
		k.UpdateDenylist(ctx, consumerId, parameters.Denylist)
	}
	if !slices.Equal(oldParameters.Prioritylist, parameters.Prioritylist) {
		k.UpdatePrioritylist(ctx, consumerId, parameters.Prioritylist)
	}

	return nil
}

// SetAllowlist allowlists validator with `providerAddr` address on chain `consumerId`
func (k Keeper) SetAllowlist(
	ctx sdk.Context,
	consumerId string,
	providerAddr types.ProviderConsAddress,
) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.AllowlistKey(consumerId, providerAddr), []byte{})
}

// GetAllowList returns all allowlisted validators
func (k Keeper) GetAllowList(
	ctx sdk.Context,
	consumerId string,
) (providerConsAddresses []types.ProviderConsAddress) {
	store := ctx.KVStore(k.storeKey)
	key := types.StringIdWithLenKey(types.AllowlistKeyPrefix(), consumerId)
	iterator := storetypes.KVStorePrefixIterator(store, key)
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		providerConsAddresses = append(providerConsAddresses, types.NewProviderConsAddress(iterator.Key()[len(key):]))
	}

	return providerConsAddresses
}

// IsAllowlisted returns `true` if validator with `providerAddr` has been allowlisted on chain `consumerId`
func (k Keeper) IsAllowlisted(
	ctx sdk.Context,
	consumerId string,
	providerAddr types.ProviderConsAddress,
) bool {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.AllowlistKey(consumerId, providerAddr))
	return bz != nil
}

// DeleteAllowlist deletes all allowlisted validators
func (k Keeper) DeleteAllowlist(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	iterator := storetypes.KVStorePrefixIterator(store, types.StringIdWithLenKey(types.AllowlistKeyPrefix(), consumerId))
	defer iterator.Close()

	keysToDel := [][]byte{}
	for ; iterator.Valid(); iterator.Next() {
		keysToDel = append(keysToDel, iterator.Key())
	}

	for _, key := range keysToDel {
		store.Delete(key)
	}
}

// IsAllowlistEmpty returns `true` if no validator is allowlisted on chain `consumerId`
func (k Keeper) IsAllowlistEmpty(ctx sdk.Context, consumerId string) bool {
	store := ctx.KVStore(k.storeKey)
	iterator := storetypes.KVStorePrefixIterator(store, types.StringIdWithLenKey(types.AllowlistKeyPrefix(), consumerId))
	defer iterator.Close()

	return !iterator.Valid()
}

// UpdateAllowlist populates the allowlist store for the consumer chain with this consumer id
func (k Keeper) UpdateAllowlist(ctx sdk.Context, consumerId string, allowlist []string) {
	k.DeleteAllowlist(ctx, consumerId)
	for _, address := range allowlist {
		consAddr, err := sdk.ConsAddressFromBech32(address)
		if err != nil {
			continue
		}

		k.SetAllowlist(ctx, consumerId, types.NewProviderConsAddress(consAddr))
	}
}

// SetDenylist denylists validator with `providerAddr` address on chain `consumerId`
func (k Keeper) SetDenylist(
	ctx sdk.Context,
	consumerId string,
	providerAddr types.ProviderConsAddress,
) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.DenylistKey(consumerId, providerAddr), []byte{})
}

// GetDenyList returns all denylisted validators
func (k Keeper) GetDenyList(
	ctx sdk.Context,
	consumerId string,
) (providerConsAddresses []types.ProviderConsAddress) {
	store := ctx.KVStore(k.storeKey)
	key := types.StringIdWithLenKey(types.DenylistKeyPrefix(), consumerId)
	iterator := storetypes.KVStorePrefixIterator(store, key)
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		providerConsAddresses = append(providerConsAddresses, types.NewProviderConsAddress(iterator.Key()[len(key):]))
	}

	return providerConsAddresses
}

// IsDenylisted returns `true` if validator with `providerAddr` has been denylisted on chain `consumerId`
func (k Keeper) IsDenylisted(
	ctx sdk.Context,
	consumerId string,
	providerAddr types.ProviderConsAddress,
) bool {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.DenylistKey(consumerId, providerAddr))
	return bz != nil
}

// DeleteDenylist deletes all denylisted validators
func (k Keeper) DeleteDenylist(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	iterator := storetypes.KVStorePrefixIterator(store, types.StringIdWithLenKey(types.DenylistKeyPrefix(), consumerId))
	defer iterator.Close()

	keysToDel := [][]byte{}
	for ; iterator.Valid(); iterator.Next() {
		keysToDel = append(keysToDel, iterator.Key())
	}

	for _, key := range keysToDel {
		store.Delete(key)
	}
}

// IsDenylistEmpty returns `true` if no validator is denylisted on chain `consumerId`
func (k Keeper) IsDenylistEmpty(ctx sdk.Context, consumerId string) bool {
	store := ctx.KVStore(k.storeKey)
	iterator := storetypes.KVStorePrefixIterator(store, types.StringIdWithLenKey(types.DenylistKeyPrefix(), consumerId))
	defer iterator.Close()

	return !iterator.Valid()
}

// UpdateDenylist populates the denylist store for the consumer chain with this consumer id
func (k Keeper) UpdateDenylist(ctx sdk.Context, consumerId string, denylist []string) {
	k.DeleteDenylist(ctx, consumerId)
	for _, address := range denylist {
		consAddr, err := sdk.ConsAddressFromBech32(address)
		if err != nil {
			continue
		}

		k.SetDenylist(ctx, consumerId, types.NewProviderConsAddress(consAddr))
	}
}

// SetMinimumPowerInTopN sets the minimum power required for a validator to be in the top N
// for a given consumer chain.
func (k Keeper) SetMinimumPowerInTopN(
	ctx sdk.Context,
	consumerId string,
	power int64,
) {
	store := ctx.KVStore(k.storeKey)

	buf := make([]byte, 8)
	binary.BigEndian.PutUint64(buf, uint64(power))

	store.Set(types.MinimumPowerInTopNKey(consumerId), buf)
}

// GetMinimumPowerInTopN returns the minimum power required for a validator to be in the top N
// for a given consumer chain.
func (k Keeper) GetMinimumPowerInTopN(
	ctx sdk.Context,
	consumerId string,
) (int64, bool) {
	store := ctx.KVStore(k.storeKey)
	buf := store.Get(types.MinimumPowerInTopNKey(consumerId))
	if buf == nil {
		return 0, false
	}
	return int64(binary.BigEndian.Uint64(buf)), true
}

// DeleteMinimumPowerInTopN removes the minimum power required for a validator to be in the top N
// for a given consumer chain.
func (k Keeper) DeleteMinimumPowerInTopN(
	ctx sdk.Context,
	consumerId string,
) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.MinimumPowerInTopNKey(consumerId))
}

// SetPrioritylist prioritylists validator with `providerAddr` address on chain `consumerId`
func (k Keeper) SetPrioritylist(
	ctx sdk.Context,
	consumerId string,
	providerAddr types.ProviderConsAddress,
) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.PrioritylistKey(consumerId, providerAddr), []byte{})
}

// GetPriorityList returns all prioritylisted validators
func (k Keeper) GetPriorityList(
	ctx sdk.Context,
	consumerId string,
) (providerConsAddresses []types.ProviderConsAddress) {
	store := ctx.KVStore(k.storeKey)
	key := types.StringIdWithLenKey(types.PrioritylistKeyPrefix(), consumerId)
	iterator := storetypes.KVStorePrefixIterator(store, key)
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		providerConsAddresses = append(providerConsAddresses, types.NewProviderConsAddress(iterator.Key()[len(key):]))
	}

	return providerConsAddresses
}

// IsPrioritylisted returns `true` if validator with `providerAddr` has been prioritylisted on chain `consumerId`
func (k Keeper) IsPrioritylisted(
	ctx sdk.Context,
	consumerId string,
	providerAddr types.ProviderConsAddress,
) bool {
	store := ctx.KVStore(k.storeKey)
	return store.Get(types.PrioritylistKey(consumerId, providerAddr)) != nil
}

// DeletePrioritylist deletes all prioritylisted validators
func (k Keeper) DeletePrioritylist(ctx sdk.Context, consumerId string) {
	store := ctx.KVStore(k.storeKey)
	iterator := storetypes.KVStorePrefixIterator(store, types.StringIdWithLenKey(types.PrioritylistKeyPrefix(), consumerId))
	defer iterator.Close()

	keysToDel := [][]byte{}
	for ; iterator.Valid(); iterator.Next() {
		keysToDel = append(keysToDel, iterator.Key())
	}

	for _, key := range keysToDel {
		store.Delete(key)
	}
}

// IsPrioritylistEmpty returns `true` if no validator is prioritylisted on chain `consumerId`
func (k Keeper) IsPrioritylistEmpty(ctx sdk.Context, consumerId string) bool {
	store := ctx.KVStore(k.storeKey)
	iterator := storetypes.KVStorePrefixIterator(store, types.StringIdWithLenKey(types.PrioritylistKeyPrefix(), consumerId))
	defer iterator.Close()

	return !iterator.Valid()
}

// UpdatePrioritylist populates the prioritylist store for the consumer chain with this consumer id
func (k Keeper) UpdatePrioritylist(ctx sdk.Context, consumerId string, prioritylist []string) {
	k.DeletePrioritylist(ctx, consumerId)
	for _, address := range prioritylist {
		consAddr, err := sdk.ConsAddressFromBech32(address)
		if err != nil {
			continue
		}

		k.SetPrioritylist(ctx, consumerId, types.NewProviderConsAddress(consAddr))
	}
}

// PartitionBasedOnPriorityList filters the priority list to include only validators that can validate the chain
// and splits the validators into priority and non-priority sets.
func (k Keeper) PartitionBasedOnPriorityList(ctx sdk.Context, consumerId string, nextValidators []types.ConsensusValidator) ([]types.ConsensusValidator, []types.ConsensusValidator) {
	priorityValidators := make([]types.ConsensusValidator, 0)
	nonPriorityValidators := make([]types.ConsensusValidator, 0)

	// Form priorityValidators
	for _, validator := range nextValidators {
		addr := types.NewProviderConsAddress(validator.ProviderConsAddr)
		if k.IsPrioritylisted(ctx, consumerId, addr) {
			priorityValidators = append(priorityValidators, validator)
		} else {
			// Add remaining validators to nonPriorityValidators
			nonPriorityValidators = append(nonPriorityValidators, validator)
		}
	}

	sort.Slice(priorityValidators, func(i, j int) bool {
		return priorityValidators[i].Power > priorityValidators[j].Power
	})

	sort.Slice(nonPriorityValidators, func(i, j int) bool {
		return nonPriorityValidators[i].Power > nonPriorityValidators[j].Power
	})

	return priorityValidators, nonPriorityValidators
}
