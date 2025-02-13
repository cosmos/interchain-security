package keeper

import (
	"fmt"

	errorsmod "cosmossdk.io/errors"
	storetypes "cosmossdk.io/store/types"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	"github.com/cosmos/interchain-security/v7/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v7/x/ccv/types"
)

// HandleOptIn prepares validator `providerAddr` to opt in to `consumerId` with an optional `consumerKey` consumer public key.
// Note that the validator only opts in at the end of an epoch.
func (k Keeper) HandleOptIn(ctx sdk.Context, consumerId string, providerAddr types.ProviderConsAddress, consumerKey string) error {
	if !k.IsConsumerActive(ctx, consumerId) {
		return errorsmod.Wrapf(
			types.ErrInvalidPhase,
			"cannot opt in to a consumer chain that is not in the registered, initialized, or launched phase: %s", consumerId)
	}

	k.SetOptedIn(ctx, consumerId, providerAddr)

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

	return nil
}

// OptInTopNValidators opts in to `consumerId` all the `bondedValidators` that have at least `minPowerToOptIn` power
func (k Keeper) OptInTopNValidators(
	ctx sdk.Context,
	consumerId string,
	bondedValidators []stakingtypes.Validator,
	minPowerToOptIn int64,
) error {
	for _, val := range bondedValidators {
		// log the validator
		k.Logger(ctx).Debug("Checking whether to opt in validator because of top N",
			"consumerId", consumerId,
			"validator", val.GetOperator(),
		)

		valAddr, err := sdk.ValAddressFromBech32(val.GetOperator())
		if err != nil {
			return fmt.Errorf("converting operator address to validator address, consumerId(%s), validator(%s): %w",
				consumerId, val.GetOperator(), err)
		}
		power, err := k.stakingKeeper.GetLastValidatorPower(ctx, valAddr)
		if err != nil {
			return fmt.Errorf("getting validator power, consumerId(%s), validator(%s): %w",
				consumerId, val.GetOperator(), err)
		}
		if power >= minPowerToOptIn {
			consAddr, err := val.GetConsAddr()
			if err != nil {
				return fmt.Errorf("getting validator consensus address, consumerId(%s), validator(%s): %w",
					consumerId, val.GetOperator(), err)
			}

			k.Logger(ctx).Debug("Opting in validator", "consumerId", consumerId, "validator", val.GetOperator())

			// if validator is already opted in, it gets overwritten
			k.SetOptedIn(ctx, consumerId, types.NewProviderConsAddress(consAddr))
		} // else validators that do not belong to the top N validators but were opted in, remain opted in
	}
	return nil
}

//
// Setters and getters
//

func (k Keeper) SetOptedIn(
	ctx sdk.Context,
	consumerId string,
	providerConsAddress types.ProviderConsAddress,
) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.OptedInKey(consumerId, providerConsAddress), []byte{})
}

func (k Keeper) DeleteOptedIn(
	ctx sdk.Context,
	consumerId string,
	providerAddr types.ProviderConsAddress,
) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.OptedInKey(consumerId, providerAddr))
}

func (k Keeper) IsOptedIn(
	ctx sdk.Context,
	consumerId string,
	providerAddr types.ProviderConsAddress,
) bool {
	store := ctx.KVStore(k.storeKey)
	return store.Get(types.OptedInKey(consumerId, providerAddr)) != nil
}

// GetAllOptedIn returns all the opted-in validators on chain `consumerId`
func (k Keeper) GetAllOptedIn(
	ctx sdk.Context,
	consumerId string,
) (providerConsAddresses []types.ProviderConsAddress) {
	store := ctx.KVStore(k.storeKey)
	key := types.StringIdWithLenKey(types.OptedInKeyPrefix(), consumerId)
	iterator := storetypes.KVStorePrefixIterator(store, key)
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		providerConsAddresses = append(providerConsAddresses, types.NewProviderConsAddress(iterator.Key()[len(key):]))
	}

	return providerConsAddresses
}

// DeleteAllOptedIn deletes all the opted-in validators for chain with `consumerId`
func (k Keeper) DeleteAllOptedIn(
	ctx sdk.Context,
	consumerId string,
) {
	store := ctx.KVStore(k.storeKey)
	key := types.StringIdWithLenKey(types.OptedInKeyPrefix(), consumerId)
	iterator := storetypes.KVStorePrefixIterator(store, key)

	var keysToDel [][]byte
	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		keysToDel = append(keysToDel, iterator.Key())
	}
	for _, delKey := range keysToDel {
		store.Delete(delKey)
	}
}
