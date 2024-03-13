package keeper

import (
	"cosmossdk.io/math"
	"fmt"
	abci "github.com/cometbft/cometbft/abci/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	"github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
	"sort"
)

// SetConsumerValidator sets provided consumer `validator` on the consumer chain with `chainID`
func (k Keeper) SetConsumerValidator(
	ctx sdk.Context,
	chainID string,
	validator types.ConsumerValidator,
) {
	store := ctx.KVStore(k.storeKey)
	bz, err := validator.Marshal()
	if err != nil {
		panic(fmt.Errorf("failed to marshal ConsumerValidator: %w", err))
	}

	store.Set(types.ConsumerValidatorKey(chainID, validator.ProviderConsAddr), bz)
}

// DeleteConsumerValidator removes consumer validator with `providerAddr` address
func (k Keeper) DeleteConsumerValidator(
	ctx sdk.Context,
	chainID string,
	providerConsAddr types.ProviderConsAddress,
) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerValidatorKey(chainID, providerConsAddr.ToSdkConsAddr()))
}

// DeleteConsumerValSet deletes all the stored consumer validators for chain `chainID`
func (k Keeper) DeleteConsumerValSet(
	ctx sdk.Context,
	chainID string) {
	store := ctx.KVStore(k.storeKey)
	key := types.ChainIdWithLenKey(types.ConsumerValidatorBytePrefix, chainID)
	iterator := sdk.KVStorePrefixIterator(store, key)

	var keysToDel [][]byte
	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		keysToDel = append(keysToDel, iterator.Key())
	}
	for _, delKey := range keysToDel {
		store.Delete(delKey)
	}
}

// IsConsumerValidator returns `true` if the consumer validator with `providerAddr` exists for chain `chainID`
// and `false` otherwise
func (k Keeper) IsConsumerValidator(
	ctx sdk.Context,
	chainID string,
	providerAddr types.ProviderConsAddress,
) bool {
	store := ctx.KVStore(k.storeKey)
	return store.Get(types.ConsumerValidatorKey(chainID, providerAddr.ToSdkConsAddr())) != nil
}

// GetConsumerValSet returns all the consumer validators for chain `chainID`
func (k Keeper) GetConsumerValSet(
	ctx sdk.Context,
	chainID string) (validators []types.ConsumerValidator) {
	store := ctx.KVStore(k.storeKey)
	key := types.ChainIdWithLenKey(types.ConsumerValidatorBytePrefix, chainID)
	iterator := sdk.KVStorePrefixIterator(store, key)
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		iterator.Value()
		var validator types.ConsumerValidator
		if err := validator.Unmarshal(iterator.Value()); err != nil {
			panic(fmt.Errorf("failed to unmarshal ConsumerValidator: %w", err))
		}
		validators = append(validators, validator)
	}

	return validators
}

// ComputeNextEpochConsumerValSet returns the next validator set that is responsible for validating consumer
// chain `chainID`, based on the bonded validators.
func (k Keeper) ComputeNextEpochConsumerValSet(
	ctx sdk.Context,
	chainID string,
	bondedValidators []stakingtypes.Validator,
) []types.ConsumerValidator {
	var nextValidators []types.ConsumerValidator
	for _, val := range bondedValidators {
		// get next voting power and the next consumer public key
		nextPower := k.stakingKeeper.GetLastValidatorPower(ctx, val.GetOperator())
		consAddr, err := val.GetConsAddr()
		if err != nil {
			// this should never happen but is recoverable if we exclude this validator from the `nextValidators`
			k.Logger(ctx).Error("could not get consensus address of validator",
				"validator", val.GetOperator().String(),
				"error", err)
			continue
		}
		nextConsumerPublicKey, foundConsumerPublicKey := k.GetValidatorConsumerPubKey(ctx, chainID, types.NewProviderConsAddress(consAddr))
		if !foundConsumerPublicKey {
			// if no consumer key assigned then use the validator's key itself
			k.Logger(ctx).Info("could not retrieve public key for validator on consumer chain because"+
				" the validator did not assign a new consumer key",
				"validator", val.GetOperator().String(),
				"chainID", chainID)
			nextConsumerPublicKey, err = val.TmConsPublicKey()
			if err != nil {
				// this should never happen and might not be recoverable because without the public key
				// we cannot generate a validator update
				panic(fmt.Errorf("could not retrieve validator's (%+v) public key: %w", val, err))
			}
		}

		nextValidator := types.ConsumerValidator{
			ProviderConsAddr:  consAddr,
			Power:             nextPower,
			ConsumerPublicKey: &nextConsumerPublicKey,
		}
		nextValidators = append(nextValidators, nextValidator)
	}

	return nextValidators
}

// DiffValidators compares the current and the next epoch's consumer validators and returns the `ValidatorUpdate` diff
// needed by CometBFT to update the validator set on a chain.
func DiffValidators(
	currentValidators []types.ConsumerValidator,
	nextValidators []types.ConsumerValidator) []abci.ValidatorUpdate {
	var updates []abci.ValidatorUpdate

	isCurrentValidator := make(map[string]types.ConsumerValidator)
	for _, val := range currentValidators {
		isCurrentValidator[val.ConsumerPublicKey.String()] = val
	}

	isNextValidator := make(map[string]types.ConsumerValidator)
	for _, val := range nextValidators {
		isNextValidator[val.ConsumerPublicKey.String()] = val
	}

	for _, currentVal := range currentValidators {
		if nextVal, found := isNextValidator[currentVal.ConsumerPublicKey.String()]; !found {
			// this consumer public key does not appear in the next validators and hence we remove the validator
			// with that consumer public key by creating an update with 0 power
			updates = append(updates, abci.ValidatorUpdate{PubKey: *currentVal.ConsumerPublicKey, Power: 0})
		} else if currentVal.Power != nextVal.Power {
			// validator did not modify its consumer public key but has changed its voting power, so we
			// have to create an update with the new power
			updates = append(updates, abci.ValidatorUpdate{PubKey: *nextVal.ConsumerPublicKey, Power: nextVal.Power})
		}
		// else no update is needed because neither the consumer public key changed, nor the power of the validator
	}

	for _, nextVal := range nextValidators {
		if _, found := isCurrentValidator[nextVal.ConsumerPublicKey.String()]; !found {
			// this consumer public key does not exist in the current validators and hence we introduce this validator
			updates = append(updates, abci.ValidatorUpdate{PubKey: *nextVal.ConsumerPublicKey, Power: nextVal.Power})
		}
	}

	return updates
}

// SetConsumerValSet resets the current consumer validators with the `nextValidators` computed by
// `ComputeNextEpochConsumerValSet` and hence this method should only be called after `ComputeNextEpochConsumerValSet` has completed.
func (k Keeper) SetConsumerValSet(ctx sdk.Context, chainID string, nextValidators []types.ConsumerValidator) {
	k.DeleteConsumerValSet(ctx, chainID)
	for _, val := range nextValidators {
		k.SetConsumerValidator(ctx, chainID, val)
	}
}

// ComputeNextEpochOptedInConsumerValSet returns the next validator set that is responsible for validating consumer
// chain `chainID`, based on the bonded validators.
func (k Keeper) ComputeNextEpochOptedInConsumerValSet(
	ctx sdk.Context,
	chainID string,
) []types.ConsumerValidator {
	var nextValidators []types.ConsumerValidator
	for _, val := range k.GetAllOptedIn(ctx, chainID) {
		// get next voting power and the next consumer public key
		providerAddress := types.ProviderConsAddress{Address: val.ProviderConsAddr}
		stakingValidator, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, providerAddress.ToSdkConsAddr())
		if !found {
			// this should never happen but is recoverable if we exclude this validator from the `nextValidators`
			k.Logger(ctx).Error("could not get consensus address of validator",
				"validator", stakingValidator.GetOperator().String())

			fmt.Println("..")
		}
		nextPower := k.stakingKeeper.GetLastValidatorPower(ctx, stakingValidator.GetOperator())
		nextConsumerPublicKey, foundConsumerPublicKey := k.GetValidatorConsumerPubKey(ctx, chainID, providerAddress)
		if !foundConsumerPublicKey {
			// if no consumer key assigned then use the validator's key itself
			k.Logger(ctx).Info("could not retrieve public key for validator on consumer chain because"+
				" the validator did not assign a new consumer key",
				"validator", stakingValidator.GetOperator().String(),
				"chainID", chainID)
			var err error
			nextConsumerPublicKey, err = stakingValidator.TmConsPublicKey()
			if err != nil {
				// this should never happen and might not be recoverable because without the public key
				// we cannot generate a validator update
				panic(fmt.Errorf("could not retrieve validator's (%+v) public key: %w", val, err))
			}
		}

		nextValidator := types.ConsumerValidator{
			ProviderConsAddr:  val.ProviderConsAddr,
			Power:             nextPower,
			ConsumerPublicKey: &nextConsumerPublicKey,
		}
		nextValidators = append(nextValidators, nextValidator)
	}

	return nextValidators
}

func (k Keeper) OptInValidators(ctx sdk.Context, chainID string, threshold math.LegacyDec, bondedValidators []stakingtypes.Validator) {
	powerStop := k.ComputePowerThreshold(ctx, bondedValidators, threshold)

	for _, val := range bondedValidators {
		power := k.stakingKeeper.GetLastValidatorPower(ctx, val.GetOperator())
		if power >= powerStop {
			consAddr, err := val.GetConsAddr()
			_ = err // fIXME
			nextConsumerPublicKey, foundConsumerPublicKey := k.GetValidatorConsumerPubKey(ctx, chainID, types.NewProviderConsAddress(consAddr))
			if !foundConsumerPublicKey {
				// if no consumer key assigned then use the validator's key itself
				k.Logger(ctx).Info("could not retrieve public key for validator on consumer chain because"+
					" the validator did not assign a new consumer key",
					"validator", val.GetOperator().String(),
					"chainID", chainID)
				nextConsumerPublicKey, err = val.TmConsPublicKey()
				if err != nil {
					// this should never happen and might not be recoverable because without the public key
					// we cannot generate a validator update
					panic(fmt.Errorf("could not retrieve validator's (%+v) public key: %w", val, err))
				}
			}
			// if validator already exists it gets overwritten
			k.SetOptedIn(ctx, chainID, types.ConsumerValidator{
				ProviderConsAddr:  consAddr,
				Power:             power,
				ConsumerPublicKey: &nextConsumerPublicKey,
			})
		} else {
			// validators that are not on the top N and habe opte din remain opted in,
		}
	}
}

func (k Keeper) ComputePowerThreshold(ctx sdk.Context,
	bondedValidators []stakingtypes.Validator,
	threshold math.LegacyDec,
) int64 {
	totalPower := int64(0)
	var powers []int64
	for _, val := range bondedValidators {
		power := k.stakingKeeper.GetLastValidatorPower(ctx, val.GetOperator())
		powers = append(powers, power)
		totalPower = totalPower + power
	}

	// sort by powers ascending
	sort.SliceStable(powers, func(i, j int) bool {
		return powers[i] < powers[j]
	})

	powerSum := sdk.ZeroDec()
	for _, power := range powers {
		powerSum = powerSum.Add(sdk.NewDecFromInt(sdk.NewInt(power)))
		if powerSum.Quo(sdk.NewDecFromInt(sdk.NewInt(totalPower))).GT(threshold) {
			return power
		}
	}

	panic("UpdateSoftOptOutThresholdPower should not reach this point. Incorrect logic!")
}
