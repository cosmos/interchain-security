package keeper

import (
	"fmt"
	abci "github.com/cometbft/cometbft/abci/types"
	"github.com/cometbft/cometbft/proto/tendermint/crypto"
	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	"github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
)

// SetEpochValidator sets provided epoch `validator` on the consumer chain with `chainID`
func (k Keeper) SetEpochValidator(
	ctx sdk.Context,
	chainID string,
	validator types.EpochValidator,
) {
	store := ctx.KVStore(k.storeKey)
	bz, err := validator.Marshal()
	if err != nil {
		panic(fmt.Errorf("failed to marshal EpochValidator: %w", err))
	}

	store.Set(types.EpochKey(chainID, validator.ProviderConsAddr), bz)
}

// DeleteEpochValidator removes epoch validator with `providerAddr` address
func (k Keeper) DeleteEpochValidator(
	ctx sdk.Context,
	chainID string,
	providerConsAddr types.ProviderConsAddress,
) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.EpochKey(chainID, providerConsAddr.ToSdkConsAddr()))
}

// DeleteAllEpochValidators deletes all the stored epoch validators
func (k Keeper) DeleteAllEpochValidators(
	ctx sdk.Context,
	chainID string) {
	store := ctx.KVStore(k.storeKey)
	key := types.ChainIdWithLenKey(types.EpochBytePrefix, chainID)
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

// IsEpochValidator returns `true` if the validator with `providerAddr` is set in and `false` otherwise
func (k Keeper) IsEpochValidator(
	ctx sdk.Context,
	chainID string,
	providerAddr types.ProviderConsAddress,
) bool {
	store := ctx.KVStore(k.storeKey)
	return store.Get(types.EpochKey(chainID, providerAddr.ToSdkConsAddr())) != nil
}

// GetAllEpochValidators returns all the epoch validators on chain `chainID`
func (k Keeper) GetAllEpochValidators(
	ctx sdk.Context,
	chainID string) (optedInValidators []types.EpochValidator) {
	store := ctx.KVStore(k.storeKey)
	key := types.ChainIdWithLenKey(types.EpochBytePrefix, chainID)
	iterator := sdk.KVStorePrefixIterator(store, key)
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		iterator.Value()
		var optedInValidator types.EpochValidator
		if err := optedInValidator.Unmarshal(iterator.Value()); err != nil {
			panic(fmt.Errorf("failed to unmarshal EpochValidator: %w", err))
		}
		optedInValidators = append(optedInValidators, optedInValidator)
	}

	return optedInValidators
}

// ComputeNextEpochValidators returns the next validator set that is responsible for validating consumer chain `chainID`,
// based on the bonded validators.
func (k Keeper) ComputeNextEpochValidators(
	ctx sdk.Context,
	chainID string,
	bondedValidators []stakingtypes.Validator,
) []types.EpochValidator {
	var nextValidators []types.EpochValidator
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

		nextConsumerPublicKeyBytes, err := nextConsumerPublicKey.Marshal()
		if err != nil {
			// this should never happen but is recoverable if we exclude this validator from the `nextValidators`
			k.Logger(ctx).Error("could not marshal consumer public key",
				"consumer public key", nextConsumerPublicKey,
				"error", err)
			continue
		}

		nextValidator := types.EpochValidator{
			ProviderConsAddr:  consAddr,
			Power:             nextPower,
			ConsumerPublicKey: nextConsumerPublicKeyBytes,
		}
		nextValidators = append(nextValidators, nextValidator)
	}

	return nextValidators
}

// DiffValidators compares the current and the next epoch validators and returns the `ValidatorUpdate` diff needed
// by CometBFT to update the validator set on a chain.
func DiffValidators(
	currentValidators []types.EpochValidator,
	nextValidators []types.EpochValidator) []abci.ValidatorUpdate {
	var updates []abci.ValidatorUpdate

	isCurrentValidator := make(map[string]types.EpochValidator)
	for _, val := range currentValidators {
		isCurrentValidator[string(val.ProviderConsAddr)] = val
	}

	isNextValidator := make(map[string]types.EpochValidator)
	for _, val := range nextValidators {
		isNextValidator[string(val.ProviderConsAddr)] = val
	}

	for _, val := range currentValidators {
		var currentPublicKey crypto.PublicKey
		err := currentPublicKey.Unmarshal(val.ConsumerPublicKey)
		if err != nil {
			// this should never happen and might not be recoverable because without the public key
			// we cannot generate a validator update
			panic(fmt.Errorf("could not unmarshall validator's (%+v) public key: %w", val, err))
		}

		if nextVal, found := isNextValidator[string(val.ProviderConsAddr)]; found {
			// validator remains in the next epoch
			var nextPublicKey crypto.PublicKey
			err = nextPublicKey.Unmarshal(nextVal.ConsumerPublicKey)
			if err != nil {
				// this should never happen and is not recoverable because without the public key
				// we cannot generate a validator update
				panic(fmt.Errorf("could not unmarshall validator's (%+v) public key: %w", nextVal, err))
			}

			if !currentPublicKey.Equal(nextPublicKey) {
				updates = append(updates, abci.ValidatorUpdate{PubKey: currentPublicKey, Power: 0})
				updates = append(updates, abci.ValidatorUpdate{PubKey: nextPublicKey, Power: nextVal.Power})
			} else if val.Power != nextVal.Power {
				updates = append(updates, abci.ValidatorUpdate{PubKey: nextPublicKey, Power: nextVal.Power})
			}
			// else no update is needed because neither the consumer public key changed, nor the power of the validator
		} else {
			// not found in next validators and hence the validator has to be removed
			updates = append(updates, abci.ValidatorUpdate{PubKey: currentPublicKey, Power: 0})
		}
	}

	for _, val := range nextValidators {
		if _, found := isCurrentValidator[string(val.ProviderConsAddr)]; !found {
			// validators that are about to join an epoch
			var nextPublicKey crypto.PublicKey
			err := nextPublicKey.Unmarshal(val.ConsumerPublicKey)
			if err != nil {
				// this should never happen and is not recoverable because without the public key
				// we cannot generate a validator update
				panic(fmt.Errorf("could not unmarshall validator's (%+v) public key: %w", val, err))
			}

			updates = append(updates, abci.ValidatorUpdate{PubKey: nextPublicKey, Power: val.Power})
		}
	}

	return updates
}

// ResetCurrentEpochValidators resets the current epoch validators with the `nextValidators` computed by
// `ComputeNextEpochValidators` and hence this method should only be called after `ComputeNextEpochValidators` has completed.
func (k Keeper) ResetCurrentEpochValidators(ctx sdk.Context, chainID string, nextValidators []types.EpochValidator) {
	k.DeleteAllEpochValidators(ctx, chainID)
	for _, val := range nextValidators {
		k.SetEpochValidator(ctx, chainID, val)
	}
}
