package keeper

import (
	errorsmod "cosmossdk.io/errors"

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
		} else {
			// validators that do not belong to the top N validators but were opted in, remain opted in
		}
	}
}

// ComputeMinPowerToOptIn returns the minimum power needed for a validator (from the bonded validators)
// to belong to the `topN` validators
func (k Keeper) ComputeMinPowerToOptIn(ctx sdk.Context, bondedValidators []stakingtypes.Validator, topN uint32) int64 {
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
	// perform an equal comparison as well (`GTE`). In any case, we do not have to panic here because we can return
	// the smallest possible power.
	k.Logger(ctx).Error("should never reach this point",
		"topN", topN,
		"totalPower", totalPower,
		"powerSum", powerSum)
	return powers[len(powers)-1]
}
