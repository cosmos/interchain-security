package keeper

import (
	"fmt"
	"sort"

	errorsmod "cosmossdk.io/errors"
	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	abci "github.com/cometbft/cometbft/abci/types"

	"github.com/cosmos/interchain-security/v6/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/v6/x/ccv/types"
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
) error {
	return k.setValidator(ctx, k.GetConsumerChainConsensusValidatorsKey(ctx, consumerId), validator)
}

// SetConsumerValSet resets the current consumer validators with the `nextValidators` computed by
// `FilterValidators` and hence this method should only be called after `FilterValidators` has completed.
func (k Keeper) SetConsumerValSet(ctx sdk.Context, consumerId string, nextValidators []types.ConsensusValidator) error {
	return k.setValSet(ctx, k.GetConsumerChainConsensusValidatorsKey(ctx, consumerId), nextValidators)
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
		consumerPublicKey, err = validator.CmtConsPublicKey()
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
	predicate func(providerAddr types.ProviderConsAddress) (bool, error),
) ([]types.ConsensusValidator, error) {
	var nextValidators []types.ConsensusValidator
	for _, val := range bondedValidators {
		consAddr, err := val.GetConsAddr()
		if err != nil {
			continue
		}

		ok, err := predicate(types.NewProviderConsAddress(consAddr))
		if err != nil {
			return nextValidators, err
		}
		if ok {
			nextValidator, err := k.CreateConsumerValidator(ctx, consumerId, val)
			if err != nil {
				return nextValidators, err
			}
			nextValidators = append(nextValidators, nextValidator)
		}
	}

	return nextValidators, nil
}

// ComputeNextValidators computes the validators for the upcoming epoch based on the currently `bondedValidators`.
func (k Keeper) ComputeNextValidators(
	ctx sdk.Context,
	consumerId string,
	bondedValidators []stakingtypes.Validator,
	powerShapingParameters types.PowerShapingParameters,
	minPowerToOptIn int64,
) ([]types.ConsensusValidator, error) {
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

	nextValidators, err := k.FilterValidators(ctx, consumerId, bondedValidators,
		func(providerAddr types.ProviderConsAddress) (bool, error) {
			canValidateChain, err := k.CanValidateChain(ctx, consumerId, providerAddr, powerShapingParameters.Top_N, minPowerToOptIn)
			if err != nil {
				return false, err
			}
			fulfillsMinStake, err := k.FulfillsMinStake(ctx, powerShapingParameters.MinStake, providerAddr)
			if err != nil {
				return false, err
			}
			return canValidateChain && fulfillsMinStake, nil
		})
	if err != nil {
		return []types.ConsensusValidator{}, err
	}

	priorityValidators, nonPriorityValidators := k.FilterAndSortPriorityList(ctx, powerShapingParameters.Prioritylist, nextValidators)

	nextValidators = k.CapValidatorSet(ctx, powerShapingParameters, append(priorityValidators, nonPriorityValidators...))

	nextValidators = k.CapValidatorsPower(ctx, powerShapingParameters.ValidatorsPowerCap, nextValidators)

	return nextValidators, nil
}

// GetLastBondedValidators iterates the last validator powers in the staking module
// and returns the first MaxValidators many validators with the largest powers.
func (k Keeper) GetLastBondedValidators(ctx sdk.Context) ([]stakingtypes.Validator, error) {
	maxVals, err := k.stakingKeeper.MaxValidators(ctx)
	if err != nil {
		return nil, err
	}
	return ccv.GetLastBondedValidatorsUtil(ctx, k.stakingKeeper, maxVals)
}

// GetLastProviderConsensusActiveValidators returns the `MaxProviderConsensusValidators` many validators with the largest powers
// from the last bonded validators in the staking module.
func (k Keeper) GetLastProviderConsensusActiveValidators(ctx sdk.Context) ([]stakingtypes.Validator, error) {
	maxVals := k.GetMaxProviderConsensusValidators(ctx)
	return ccv.GetLastBondedValidatorsUtil(ctx, k.stakingKeeper, uint32(maxVals))
}

// ComputeConsumerNextValSet computes the consumer next validator set and returns
// the validator updates to be sent to the consumer chain.
// For TopN consumer chains, it automatically opts in all validators that
// belong to the top N of the active validators.
//
// TODO add unit test for ComputeConsumerNextValSet
func (k Keeper) ComputeConsumerNextValSet(
	ctx sdk.Context,
	bondedValidators []stakingtypes.Validator,
	activeValidators []stakingtypes.Validator,
	consumerId string,
	currentConsumerValSet []types.ConsensusValidator,
) ([]abci.ValidatorUpdate, error) {
	powerShapingParameters, err := k.GetConsumerPowerShapingParameters(ctx, consumerId)
	if err != nil {
		return []abci.ValidatorUpdate{},
			errorsmod.Wrapf(ccv.ErrInvalidConsumerState, "getting power shaping parameters: %s", err.Error())
	}

	minPower := int64(0)
	if powerShapingParameters.Top_N > 0 {
		minPower, err = k.ComputeMinPowerInTopN(ctx, activeValidators, powerShapingParameters.Top_N)
		if err != nil {
			return []abci.ValidatorUpdate{},
				fmt.Errorf("computing min power to opt in, consumerId(%s): %w", consumerId, err)
		}

		// set the minimal power of validators in the top N in the store
		k.SetMinimumPowerInTopN(ctx, consumerId, minPower)

		// in a Top-N chain, we automatically opt in all validators that belong to the top N
		// of the active validators
		err = k.OptInTopNValidators(ctx, consumerId, activeValidators, minPower)
		if err != nil {
			return []abci.ValidatorUpdate{},
				fmt.Errorf("opting in topN validators, consumerId(%s), minPower(%d): %w", consumerId, minPower, err)
		}
	}

	// need to use the bondedValidators, not activeValidators, here since the chain might be opt-in and allow inactive vals
	nextValidators, err := k.ComputeNextValidators(ctx, consumerId, bondedValidators, powerShapingParameters, minPower)
	if err != nil {
		return []abci.ValidatorUpdate{},
			fmt.Errorf("computing next validators, consumerId(%s), minPower(%d): %w", consumerId, minPower, err)
	}

	err = k.SetConsumerValSet(ctx, consumerId, nextValidators)
	if err != nil {
		return []abci.ValidatorUpdate{},
			fmt.Errorf("setting consumer validator set, consumerId(%s): %w", consumerId, err)
	}

	// get the initial updates with the latest set consumer public keys
	valUpdates := DiffValidators(currentConsumerValSet, nextValidators)

	return valUpdates, nil
}
