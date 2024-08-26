package keeper

import (
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	abci "github.com/cometbft/cometbft/abci/types"

	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/v5/x/ccv/types"
)

// GetConsumerChainConsensusValidatorsKey returns the store key for consumer validators of the consumer chain with `consumerId`
func (k Keeper) GetConsumerChainConsensusValidatorsKey(ctx sdk.Context, consumerId string) []byte {
	return types.StringIdWithLenKey(types.ConsumerValidatorKeyPrefix(), consumerId)
}

// SetConsumerValidator sets provided consumer `validator` on the consumer chain with `consumerId`
func (k Keeper) SetConsumerValidator(
	ctx sdk.Context,
	consumerId string,
	validator types.ConsensusValidator,
) {
	k.setValidator(ctx, k.GetConsumerChainConsensusValidatorsKey(ctx, consumerId), validator)
}

// SetConsumerValSet resets the current consumer validators with the `nextValidators` computed by
// `FilterValidators` and hence this method should only be called after `FilterValidators` has completed.
func (k Keeper) SetConsumerValSet(ctx sdk.Context, consumerId string, nextValidators []types.ConsensusValidator) {
	k.setValSet(ctx, k.GetConsumerChainConsensusValidatorsKey(ctx, consumerId), nextValidators)
}

// DeleteConsumerValidator removes consumer validator with `providerAddr` address
func (k Keeper) DeleteConsumerValidator(
	ctx sdk.Context,
	consumerId string,
	providerConsAddr types.ProviderConsAddress,
) {
	k.deleteValidator(ctx, k.GetConsumerChainConsensusValidatorsKey(ctx, consumerId), providerConsAddr)
}

// DeleteConsumerValSet deletes all the stored consumer validators for chain with `consumerId`
func (k Keeper) DeleteConsumerValSet(
	ctx sdk.Context,
	consumerId string,
) {
	k.deleteValSet(ctx, k.GetConsumerChainConsensusValidatorsKey(ctx, consumerId))
}

// IsConsumerValidator returns `true` if the consumer validator with `providerAddr` exists for chain with `consumerId`
// and `false` otherwise
func (k Keeper) IsConsumerValidator(ctx sdk.Context, consumerId string, providerAddr types.ProviderConsAddress) bool {
	return k.isValidator(ctx, k.GetConsumerChainConsensusValidatorsKey(ctx, consumerId), providerAddr)
}

// GetConsumerValidator returns the consumer validator with `providerAddr` if it exists for chain with `consumerId`
func (k Keeper) GetConsumerValidator(ctx sdk.Context, consumerId string, providerAddr types.ProviderConsAddress) (types.ConsensusValidator, bool) {
	store := ctx.KVStore(k.storeKey)
	marshalledConsumerValidator := store.Get(types.ConsumerValidatorKey(consumerId, providerAddr.ToSdkConsAddr()))

	if marshalledConsumerValidator == nil {
		return types.ConsensusValidator{}, false
	}

	var validator types.ConsensusValidator
	if err := validator.Unmarshal(marshalledConsumerValidator); err != nil {
		panic(fmt.Errorf("failed to unmarshal ConsumerValidator: %w", err))
	}

	return validator, true
}

// GetConsumerValSet returns all the consumer validators for chain with `consumerId`
func (k Keeper) GetConsumerValSet(
	ctx sdk.Context,
	consumerId string,
) ([]types.ConsensusValidator, error) {
	return k.getValSet(ctx, k.GetConsumerChainConsensusValidatorsKey(ctx, consumerId))
}

// DiffValidators compares the current and the next epoch's consumer validators and returns the `ValidatorUpdate` diff
// needed by CometBFT to update the validator set on a chain.
func DiffValidators(
	currentValidators []types.ConsensusValidator,
	nextValidators []types.ConsensusValidator,
) []abci.ValidatorUpdate {
	var updates []abci.ValidatorUpdate

	isCurrentValidator := make(map[string]types.ConsensusValidator, len(currentValidators))
	for _, val := range currentValidators {
		isCurrentValidator[val.PublicKey.String()] = val
	}

	isNextValidator := make(map[string]types.ConsensusValidator, len(nextValidators))
	for _, val := range nextValidators {
		isNextValidator[val.PublicKey.String()] = val
	}

	for _, currentVal := range currentValidators {
		if nextVal, found := isNextValidator[currentVal.PublicKey.String()]; !found {
			// this consumer public key does not appear in the next validators and hence we remove the validator
			// with that consumer public key by creating an update with 0 power
			updates = append(updates, abci.ValidatorUpdate{PubKey: *currentVal.PublicKey, Power: 0})
		} else if currentVal.Power != nextVal.Power {
			// validator did not modify its consumer public key but has changed its voting power, so we
			// have to create an update with the new power
			updates = append(updates, abci.ValidatorUpdate{PubKey: *nextVal.PublicKey, Power: nextVal.Power})
		}
		// else no update is needed because neither the consumer public key changed, nor the power of the validator
	}

	for _, nextVal := range nextValidators {
		if _, found := isCurrentValidator[nextVal.PublicKey.String()]; !found {
			// this consumer public key does not exist in the current validators and hence we introduce this validator
			updates = append(updates, abci.ValidatorUpdate{PubKey: *nextVal.PublicKey, Power: nextVal.Power})
		}
	}

	return updates
}

// CreateConsumerValidator creates a consumer validator for `consumerId` from the given staking `validator`
func (k Keeper) CreateConsumerValidator(ctx sdk.Context, consumerId string, validator stakingtypes.Validator) (types.ConsensusValidator, error) {
	valAddr, err := sdk.ValAddressFromBech32(validator.GetOperator())
	if err != nil {
		return types.ConsensusValidator{}, err
	}
	power, err := k.stakingKeeper.GetLastValidatorPower(ctx, valAddr)
	if err != nil {
		return types.ConsensusValidator{}, fmt.Errorf("could not retrieve validator's (%+v) power: %w",
			validator, err)
	}
	consAddr, err := validator.GetConsAddr()
	if err != nil {
		return types.ConsensusValidator{}, fmt.Errorf("could not retrieve validator's (%+v) consensus address: %w",
			validator, err)
	}

	consumerPublicKey, found := k.GetValidatorConsumerPubKey(ctx, consumerId, types.NewProviderConsAddress(consAddr))
	if !found {
		consumerPublicKey, err = validator.TmConsPublicKey()
		if err != nil {
			return types.ConsensusValidator{}, fmt.Errorf("could not retrieve validator's (%+v) public key: %w", validator, err)
		}
	}

	height := ctx.BlockHeight()
	if v, found := k.GetConsumerValidator(ctx, consumerId, types.ProviderConsAddress{Address: consAddr}); found {
		// if validator was already a consumer validator, then do not update the height set the first time
		// the validator became a consumer validator
		height = v.JoinHeight
	}

	return types.ConsensusValidator{
		ProviderConsAddr: consAddr,
		Power:            power,
		PublicKey:        &consumerPublicKey,
		JoinHeight:       height,
	}, nil
}

// FilterValidators filters the provided `bondedValidators` according to `predicate` and returns
// the filtered set.
func (k Keeper) FilterValidators(
	ctx sdk.Context,
	consumerId string,
	bondedValidators []stakingtypes.Validator,
	predicate func(providerAddr types.ProviderConsAddress) bool,
) []types.ConsensusValidator {
	var nextValidators []types.ConsensusValidator
	for _, val := range bondedValidators {
		consAddr, err := val.GetConsAddr()
		if err != nil {
			continue
		}

		if predicate(types.NewProviderConsAddress(consAddr)) {
			nextValidator, err := k.CreateConsumerValidator(ctx, consumerId, val)
			if err != nil {
				// this should never happen but is recoverable if we exclude this validator from the next validator set
				k.Logger(ctx).Error("could not create consumer validator",
					"validator", val.GetOperator(),
					"error", err)
				continue
			}

			nextValidators = append(nextValidators, nextValidator)
		}
	}

	return nextValidators
}

// GetLastBondedValidators iterates the last validator powers in the staking module
// and returns the first MaxValidators many validators with the largest powers.
func (k Keeper) GetLastBondedValidators(ctx sdk.Context) ([]stakingtypes.Validator, error) {
	maxVals, err := k.stakingKeeper.MaxValidators(ctx)
	if err != nil {
		return nil, err
	}
	return ccv.GetLastBondedValidatorsUtil(ctx, k.stakingKeeper, k.Logger(ctx), maxVals)
}

// GetLastProviderConsensusActiveValidators returns the `MaxProviderConsensusValidators` many validators with the largest powers
// from the last bonded validators in the staking module.
func (k Keeper) GetLastProviderConsensusActiveValidators(ctx sdk.Context) ([]stakingtypes.Validator, error) {
	maxVals := k.GetMaxProviderConsensusValidators(ctx)
	return ccv.GetLastBondedValidatorsUtil(ctx, k.stakingKeeper, k.Logger(ctx), uint32(maxVals))
}
