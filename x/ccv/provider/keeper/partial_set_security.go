package keeper

import (
	errorsmod "cosmossdk.io/errors"
	"cosmossdk.io/math"
	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	"github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
	"sort"
)

// HandleOptIn prepares validator `providerAddr` to opt in to `chainID` with an optional `consumerKey` consumer public key.
// Note that the validator only opts in at the end of an epoch.
func (k Keeper) HandleOptIn(ctx sdk.Context, chainID string, providerAddr types.ProviderConsAddress, consumerKey *string) error {
	if !k.IsConsumerProposedOrRegistered(ctx, chainID) {
		return errorsmod.Wrapf(
			types.ErrUnknownConsumerChainId,
			"opting in to an unknown consumer chain, with id: %s", chainID)
	}

	if k.IsToBeOptedOut(ctx, chainID, providerAddr) {
		// a validator to be opted in cancels out with a validator to be opted out
		k.DeleteToBeOptedOut(ctx, chainID, providerAddr)
	} else if !k.IsToBeOptedIn(ctx, chainID, providerAddr) && !k.IsOptedIn(ctx, chainID, providerAddr) {
		// a validator can only be set for opt in if it is not opted in and not already set for opt in
		k.SetToBeOptedIn(ctx, chainID, providerAddr)
	}

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

	if k.IsToBeOptedIn(ctx, chainID, providerAddr) {
		// a validator to be opted out cancels out a validator to be opted in
		k.DeleteToBeOptedIn(ctx, chainID, providerAddr)
	} else if !k.IsToBeOptedOut(ctx, chainID, providerAddr) && k.IsOptedIn(ctx, chainID, providerAddr) {
		// a validator can only be set for opt out if it is opted in and not already set for opt out
		k.SetToBeOptedOut(ctx, chainID, providerAddr)
	}

	return nil
}

// OptInToBeOptedInValidators opts in all the to-be-opted-in validators at the end of an epoch.
// Note that validators that are not currently active can still opt in but are filtered out at a later stage
// (e.g., `ComputeNextEpochConsumerValSet`) before we send the validator set to a consumer chain.
func (k Keeper) OptInToBeOptedInValidators(ctx sdk.Context, chainID string) {
	for _, providerConsAddress := range k.GetAllToBeOptedIn(ctx, chainID) {
		stakingValidator, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, providerConsAddress.ToSdkConsAddr())
		if !found {
			// this should never happen but is recoverable if we do not opt in this validator
			k.Logger(ctx).Error("could not get validator by consensus address",
				"consensus address", providerConsAddress.ToSdkConsAddr())
			continue
		}

		consumerValidator, err := k.CreateConsumerValidator(ctx, chainID, stakingValidator)
		if err != nil {
			k.Logger(ctx).Error("could not create consumer validator",
				"validator", stakingValidator.GetOperator().String(),
				"error", err)
			continue
		}

		// if validator already exists it gets overwritten
		k.SetOptedIn(ctx, chainID, consumerValidator)
	}

	k.DeleteAllToBeOptedIn(ctx, chainID)
}

// OptInToBeOptedInValidators opts out all the to-be-opted-out validators at the end of an epoch.
func (k Keeper) OptOutToBeOptedOutValidators(ctx sdk.Context, chainID string) {
	for _, providerConsAddress := range k.GetAllToBeOptedOut(ctx, chainID) {
		k.DeleteOptedIn(ctx, chainID, providerConsAddress)
	}

	k.DeleteAllToBeOptedOut(ctx, chainID)
}

// OptInTopNValidators opts in to `chainID` all the active validators that have power greater or equal to `powerThreshold`
func (k Keeper) OptInTopNValidators(ctx sdk.Context, chainID string, powerThreshold int64) {
	for _, val := range k.stakingKeeper.GetLastValidators(ctx) {
		power := k.stakingKeeper.GetLastValidatorPower(ctx, val.GetOperator())
		if power >= powerThreshold {
			consumerValidator, err := k.CreateConsumerValidator(ctx, chainID, val)
			if err != nil {
				k.Logger(ctx).Error("could not create consumer validator",
					"validator", val.GetOperator().String(),
					"error", err)
				continue
			}
			// if validator already exists it gets overwritten
			k.SetOptedIn(ctx, chainID, consumerValidator)
		} else {
			// validators that do not belong to the top N validators but were opted in, remain opted in
		}
	}
}

// ComputePowerThreshold returns the Nth percentile based on the given `threshold`
func (k Keeper) ComputePowerThreshold(ctx sdk.Context, topN math.LegacyDec) int64 {
	totalPower := sdk.ZeroDec()
	var powers []int64

	k.stakingKeeper.IterateLastValidatorPowers(ctx, func(addr sdk.ValAddress, power int64) (stop bool) {
		powers = append(powers, power)
		totalPower = totalPower.Add(sdk.NewDecFromInt(sdk.NewInt(power)))
		return false
	})

	// sort by powers descending
	sort.Slice(powers, func(i, j int) bool {
		return powers[i] > powers[j]
	})

	powerSum := sdk.ZeroDec()
	for _, power := range powers {
		powerSum = powerSum.Add(sdk.NewDecFromInt(sdk.NewInt(power)))
		if powerSum.Quo(totalPower).GTE(topN) {
			return power
		}
	}

	// We should never reach this point because the topN can be up to 1.0 (100%) and in the above `for` loop we
	// perform an equal comparison as well (`GTE`). In any case, we do not have to panic here because we can return
	// the smallest possible power.
	k.Logger(ctx).Error("should never reach this point",
		"topN", topN,
		"totalPower", totalPower,
		"powerSum", powerSum)
	return powers[len(powers)-1]
}
