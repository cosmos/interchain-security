package keeper

import (
	"fmt"

	errorsmod "cosmossdk.io/errors"
	storetypes "cosmossdk.io/store/types"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	"github.com/cosmos/interchain-security/v6/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v6/x/ccv/types"
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

// IsValidatorOptedInToChainId checks if the validator with `providerAddr` is opted into the chain with the specified `chainId`.
// It returns `found == true` and the corresponding chain's `consumerId` if the validator is opted in. Otherwise, it returns an empty string
// for `consumerId` and `found == false`.
func (k Keeper) IsValidatorOptedInToChainId(ctx sdk.Context, providerAddr types.ProviderConsAddress, chainId string) (string, bool) {
	consumers, err := k.GetOptedInConsumerIds(ctx, providerAddr)
	if err != nil {
		k.Logger(ctx).Error("failed to retrieve the consumer ids this validator is opted in to",
			"providerAddr", providerAddr,
			"error", err)
		return "", false
	}

	for _, consumerId := range consumers.Ids {
		consumerChainId, err := k.GetConsumerChainId(ctx, consumerId)
		if err != nil {
			k.Logger(ctx).Error("cannot find chain id",
				"consumerId", consumerId,
				"error", err)
			continue
		}

		if consumerChainId == chainId {
			return consumerId, true
		}

	}
	return "", false
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

// GetOptedInConsumerIds returns all the consumer ids where the given validator is opted in
func (k Keeper) GetOptedInConsumerIds(ctx sdk.Context, providerAddr types.ProviderConsAddress) (types.ConsumerIds, error) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ProviderConsAddrToOptedInConsumerIdsKey(providerAddr))
	if bz == nil {
		return types.ConsumerIds{}, nil
	}

	var consumerIds types.ConsumerIds
	if err := consumerIds.Unmarshal(bz); err != nil {
		return types.ConsumerIds{}, fmt.Errorf("failed to unmarshal consumer ids: %w", err)
	}

	return consumerIds, nil
}

// AppendOptedInConsumerId appends given consumer id to the list of consumers that validator has opted in
// TODO (PERMISSIONLESS) -- combine it with SetOptedIn
func (k Keeper) AppendOptedInConsumerId(ctx sdk.Context, providerAddr types.ProviderConsAddress, consumerId string) error {
	store := ctx.KVStore(k.storeKey)

	consumers, err := k.GetOptedInConsumerIds(ctx, providerAddr)
	if err != nil {
		return err
	}

	consumersWithAppend := types.ConsumerIds{
		Ids: append(consumers.Ids, consumerId),
	}

	bz, err := consumersWithAppend.Marshal()
	if err != nil {
		return err
	}

	store.Set(types.ProviderConsAddrToOptedInConsumerIdsKey(providerAddr), bz)
	return nil
}

// RemoveOptedInConsumerId removes the consumer id from this validator because it is not opted in anymore
func (k Keeper) RemoveOptedInConsumerId(ctx sdk.Context, providerAddr types.ProviderConsAddress, consumerId string) error {
	store := ctx.KVStore(k.storeKey)

	consumers, err := k.GetOptedInConsumerIds(ctx, providerAddr)
	if err != nil {
		return err
	}

	if len(consumers.Ids) == 0 {
		return fmt.Errorf("no consumer ids found for this provviderAddr: %s", providerAddr.String())
	}

	// find the index of the consumer we want to remove
	index := -1
	for i := 0; i < len(consumers.Ids); i++ {
		if consumers.Ids[i] == consumerId {
			index = i
			break
		}
	}

	if index == -1 {
		return fmt.Errorf("failed to find consumer id (%s)", consumerId)
	}

	if len(consumers.Ids) == 1 {
		store.Delete(types.ProviderConsAddrToOptedInConsumerIdsKey(providerAddr))
		return nil
	}

	consumersWithRemoval := types.ConsumerIds{
		Ids: append(consumers.Ids[:index], consumers.Ids[index+1:]...),
	}

	bz, err := consumersWithRemoval.Marshal()
	if err != nil {
		return err
	}

	store.Set(types.ProviderConsAddrToOptedInConsumerIdsKey(providerAddr), bz)
	return nil
}
