package keeper

import (
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	abci "github.com/cometbft/cometbft/abci/types"

	"github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
)

func (k Keeper) GetConsumerChainKey(ctx sdk.Context, chainID string) []byte {
	return types.ChainIdWithLenKey(types.ConsumerValidatorBytePrefix, chainID)
}

// SetConsumerValidator sets provided consumer `validator` on the consumer chain with `chainID`
func (k Keeper) SetConsumerValidator(
	ctx sdk.Context,
	chainID string,
	validator types.ConsumerValidator,
) {
	k.setValidator(ctx, k.GetConsumerChainKey(ctx, chainID), validator)
}

// SetConsumerValSet resets the current consumer validators with the `nextValidators` computed by
// `FilterValidators` and hence this method should only be called after `FilterValidators` has completed.
func (k Keeper) SetConsumerValSet(ctx sdk.Context, chainID string, nextValidators []types.ConsumerValidator) {
	k.setValSet(ctx, k.GetConsumerChainKey(ctx, chainID), nextValidators)
}

// DeleteConsumerValidator removes consumer validator with `providerAddr` address
func (k Keeper) DeleteConsumerValidator(
	ctx sdk.Context,
	chainID string,
	providerConsAddr types.ProviderConsAddress,
) {
	k.deleteValidator(ctx, k.GetConsumerChainKey(ctx, chainID), providerConsAddr)
}

// DeleteConsumerValSet deletes all the stored consumer validators for chain `chainID`
func (k Keeper) DeleteConsumerValSet(
	ctx sdk.Context,
	chainID string,
) {
	k.deleteValSet(ctx, k.GetConsumerChainKey(ctx, chainID))
}

// IsConsumerValidator returns `true` if the consumer validator with `providerAddr` exists for chain `chainID`
// and `false` otherwise
func (k Keeper) IsConsumerValidator(ctx sdk.Context, chainID string, providerAddr types.ProviderConsAddress) bool {
	return k.isValidator(ctx, k.GetConsumerChainKey(ctx, chainID), providerAddr)
}

// GetConsumerValSet returns all the consumer validators for chain `chainID`
func (k Keeper) GetConsumerValSet(
	ctx sdk.Context,
	chainID string,
) []types.ConsumerValidator {
	return k.getValSet(ctx, k.GetConsumerChainKey(ctx, chainID))
}

// DiffValidators compares the current and the next epoch's consumer validators and returns the `ValidatorUpdate` diff
// needed by CometBFT to update the validator set on a chain.
func DiffValidators(
	currentValidators []types.ConsumerValidator,
	nextValidators []types.ConsumerValidator,
) []abci.ValidatorUpdate {
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

// CreateConsumerValidator creates a consumer validator for `chainID` from the given staking `validator`
func (k Keeper) CreateConsumerValidator(ctx sdk.Context, chainID string, validator stakingtypes.Validator) (types.ConsumerValidator, error) {
	power := k.stakingKeeper.GetLastValidatorPower(ctx, validator.GetOperator())
	consAddr, err := validator.GetConsAddr()
	if err != nil {
		return types.ConsumerValidator{}, fmt.Errorf("could not retrieve validator's (%+v) consensus address: %w",
			validator, err)
	}

	consumerPublicKey, foundConsumerPublicKey := k.GetValidatorConsumerPubKey(ctx, chainID, types.NewProviderConsAddress(consAddr))
	if !foundConsumerPublicKey {
		consumerPublicKey, err = validator.TmConsPublicKey()
		if err != nil {
			return types.ConsumerValidator{}, fmt.Errorf("could not retrieve validator's (%+v) public key: %w", validator, err)
		}
	}

	return types.ConsumerValidator{
		ProviderConsAddr:  consAddr,
		Power:             power,
		ConsumerPublicKey: &consumerPublicKey,
	}, nil
}

// FilterValidators filters the provided `bondedValidators` according to `predicate` and returns
// the filtered set.
func (k Keeper) FilterValidators(
	ctx sdk.Context,
	chainID string,
	bondedValidators []stakingtypes.Validator,
	predicate func(providerAddr types.ProviderConsAddress) bool,
) []types.ConsumerValidator {
	var nextValidators []types.ConsumerValidator
	for _, val := range bondedValidators {
		consAddr, err := val.GetConsAddr()
		if err != nil {
			continue
		}

		if predicate(types.NewProviderConsAddress(consAddr)) {
			nextValidator, err := k.CreateConsumerValidator(ctx, chainID, val)
			if err != nil {
				// this should never happen but is recoverable if we exclude this validator from the next validator set
				k.Logger(ctx).Error("could not create consumer validator",
					"validator", val.GetOperator().String(),
					"error", err)
				continue
			}

			nextValidators = append(nextValidators, nextValidator)
		}
	}

	return nextValidators
}
