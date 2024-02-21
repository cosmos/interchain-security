package keeper

import (
	"fmt"
	abci "github.com/cometbft/cometbft/abci/types"
	"github.com/cometbft/cometbft/proto/tendermint/crypto"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
)

// SetOptedIn sets validator `providerAddr` as opted in with the given `blockHeight` and `power`
func (k Keeper) SetOptedIn(
	ctx sdk.Context,
	chainID string,
	validator types.CurrentEpochOptedInValidator,
) {
	store := ctx.KVStore(k.storeKey)
	bz, err := validator.Marshal()
	if err != nil {
		panic(fmt.Errorf("failed to marshal CurrentEpochOptedInValidator: %w", err))
	}

	store.Set(types.OptedInKey(chainID, validator.ProviderConsAddr), bz)
}

// DeleteOptedIn deletes opted-in validator `providerAddr`
func (k Keeper) DeleteOptedIn(
	ctx sdk.Context,
	chainID string,
	providerAddr types.ProviderConsAddress,
) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.OptedInKey(chainID, providerAddr.ToSdkConsAddr()))
}

// DeleteAllOptedIn deletes all opted-in validators
func (k Keeper) DeleteAllOptedIn(
	ctx sdk.Context,
	chainID string) {
	store := ctx.KVStore(k.storeKey)
	key := types.ChainIdWithLenKey(types.OptedInBytePrefix, chainID)
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

// IsOptedIn returns `true` if the validator with `providerAddr` is opted in and `false` otherwise
func (k Keeper) IsOptedIn(
	ctx sdk.Context,
	chainID string,
	providerAddr types.ProviderConsAddress,
) bool {
	store := ctx.KVStore(k.storeKey)
	return store.Get(types.OptedInKey(chainID, providerAddr.ToSdkConsAddr())) != nil
}

// GetAllOptedIn returns all the opted-in validators on chain `chainID`
func (k Keeper) GetAllOptedIn(
	ctx sdk.Context,
	chainID string) (optedInValidators []types.CurrentEpochOptedInValidator) {
	store := ctx.KVStore(k.storeKey)
	key := types.ChainIdWithLenKey(types.OptedInBytePrefix, chainID)
	iterator := sdk.KVStorePrefixIterator(store, key)
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		iterator.Value()
		var optedInValidator types.CurrentEpochOptedInValidator
		if err := optedInValidator.Unmarshal(iterator.Value()); err != nil {
			panic(fmt.Errorf("failed to unmarshal CurrentEpochOptedInValidator: %w", err))
		}
		optedInValidators = append(optedInValidators, optedInValidator)
	}

	return optedInValidators
}

// ComputeValidatorUpdatesAndNextValidators returns the validator updates needed to be sent to the consumer chain to
// capture the newly opted-in and opted-out validators, as well as validators that unbonded. It also computes the
// next validator set that is responsible for validating on a consumer chain.
//func (k Keeper) ComputeValidatorUpdatesAndNextValidators(ctx sdk.Context,
//	chainID string,
//	currentValidators []types.OptedInValidator,
//	validatorAddressesToAdd []types.ProviderConsAddress,
//	validatorAddressesToRemove []types.ProviderConsAddress,
//) (updates []abci.ValidatorUpdate, nextValidators []types.OptedInValidator) {
//	// store in a map all the validators that are to be removed, so we can filter out those
//	// validators when we go through `currentValidators`
//	isRemoved := make(map[string]bool)
//	for _, addr := range validatorAddressesToRemove {
//		isRemoved[addr.String()] = true
//	}
//
//	// go through all opted-in validators and look in the following order:
//	// - if the validator has opted out, generate a 0-power update
//	// - if the validator is not bonded anymore, generate a 0-power update
//	// - if the validator has changed its consumer key since last epoch, generate a 0-power update for the old key
//	//   and generate an update with the new power and the new key
//	// - if the validator has not changed its consumer key but has changed its voting power since last epoch,
//	//   generate an update with the new power
//	// - if validator has not changed its consumer key or its voting power since, then do not generate an update
//	for _, val := range currentValidators {
//		// `currentPublicKey` is the currently used key by validator `val` when validating on the consumer chain
//		var currentPublicKey crypto.PublicKey
//		err := currentPublicKey.Unmarshal(val.PublicKey)
//		if err != nil {
//			// this should never happen and is not recoverable because without the public key
//			// we cannot generate a validator update to remove this validator
//			panic(fmt.Errorf("could not unmarshall public key (%s): %w", val.PublicKey, err))
//		}
//
//		providerAddr := types.NewProviderConsAddress(val.ProviderAddr)
//		if isRemoved[providerAddr.String()] {
//			// if the validator is removed, then generate a 0-power update to remove
//			// validator `val` from the consumer chain
//			updates = append(updates, abci.ValidatorUpdate{PubKey: currentPublicKey, Power: 0})
//			continue
//		}
//
//		validator, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, val.ProviderAddr)
//		if !found {
//			// This should never happen because when `val` was added as an opt-in validator it was bonded
//			// and for it not to be found it means that it fully unbonded after an unbonding period. Assuming
//			// an epoch is smaller than the unbonding period, we would have already removed this validator from
//			// an opted-in validator. In any case, we can still recover in this case by sending a 0-power update.
//			k.Logger(ctx).Error("validator with consensus address (%s) could not be found", val.ProviderAddr)
//			updates = append(updates, abci.ValidatorUpdate{PubKey: currentPublicKey, Power: 0})
//			continue
//		}
//
//		nextPower := k.stakingKeeper.GetLastValidatorPower(ctx, validator.GetOperator())
//		if nextPower == 0 {
//			// if the validator is not bonded anymore, then send an update with 0 power to remove validator
//			updates = append(updates, abci.ValidatorUpdate{PubKey: currentPublicKey, Power: 0})
//			continue
//		}
//
//		// get the consumer key the validator intends to use to validate on the consumer chain
//		nextPublicKey, found := k.GetValidatorConsumerPubKey(ctx, chainID, types.NewProviderConsAddress(val.ProviderAddr))
//		if !found {
//			// if not found, then the current consumer key is the same
//			// as the one the validator used when it first opted in
//			nextPublicKey = currentPublicKey
//		}
//
//		if !nextPublicKey.Equal(currentPublicKey) {
//			// if the validator has changed its consumer key since last it opted in, then generate a 0-power update
//			// for the old consumer key, and an update with the new key with the new power
//			updates = append(updates, abci.ValidatorUpdate{PubKey: currentPublicKey, Power: 0})
//			updates = append(updates, abci.ValidatorUpdate{PubKey: nextPublicKey, Power: nextPower})
//		} else if val.Power != nextPower {
//			// otherwise, only send an update if the power has changed since the last epoch
//			updates = append(updates, abci.ValidatorUpdate{PubKey: nextPublicKey, Power: nextPower})
//		}
//
//		// update validator with the new power the validator has
//		// at the end of this epoch and with the new key
//		val.Power = nextPower
//		val.PublicKey, err = nextPublicKey.Marshal()
//		if err != nil {
//			// this should never happen and would lead to `panic` later on when we try to `Unmarshal` the key
//			panic(fmt.Errorf("could not marshal public key (%s): %w", nextPublicKey, err))
//		}
//
//		// validator `val` was not removed, so it would still be part of the next opted-in validators
//		nextValidators = append(nextValidators, val)
//	}
//
//	// go through all to-be-opted-in validators and look in the following order:
//	// - if the validator is not in the active set, do not generate an update for it
//	for _, addr := range validatorAddressesToAdd {
//		validator, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, addr.ToSdkConsAddr())
//		if !found {
//			k.Logger(ctx).Info("validator (%s) that was to-be-opted-in cannot be found anymore", addr)
//			continue
//		}
//
//		if !validator.IsBonded() {
//			// if the validator is not bonded anymore and hence not in the active set we do not add it
//			continue
//		}
//
//		// for a validator that just opts in, we can immediately use the next key
//		nextPublicKey, found := k.GetValidatorConsumerPubKey(ctx, chainID, addr)
//		if !found {
//			var err error
//			nextPublicKey, err = validator.TmConsPublicKey()
//			if err != nil {
//				k.Logger(ctx).Error("could not retrieve public key from validator (%s)", addr)
//				continue
//			}
//		}
//
//		// for a validator that just opts in, we can immediately use the next power
//		nextPower := k.stakingKeeper.GetLastValidatorPower(ctx, validator.GetOperator())
//		updates = append(updates, abci.ValidatorUpdate{PubKey: nextPublicKey, Power: nextPower})
//
//		nextPublicKeyBytes, err := nextPublicKey.Marshal()
//		if err != nil {
//			// this should never happen and would lead to `panic` later on when we try to `Unmarshal` the key
//			panic(fmt.Errorf("could not marshal public key (%s): %w", nextPublicKey, err))
//		}
//
//		nextValidators = append(nextValidators,
//			types.OptedInValidator{
//				ProviderAddr: addr.ToSdkConsAddr(),
//				BlockHeight:  ctx.BlockHeight(),
//				// validator that just opted-in would be using next power and next key for the upcoming epoch
//				Power:     nextPower,
//				PublicKey: nextPublicKeyBytes,
//			})
//	}
//
//	return updates, nextValidators
//}

// ComputeNextEpochOptedInValidators returns the next validator set that is responsible for validating on
// a consumer chain.
func (k Keeper) ComputeNextEpochOptedInValidators(
	ctx sdk.Context,
	chainID string,
	currentValidators []types.CurrentEpochOptedInValidator,
) (nextValidators []types.CurrentEpochOptedInValidator) {
	for _, val := range currentValidators {
		// `currentPublicKey` is the currently used key by validator `val` when validating on the consumer chain
		var currentPublicKey crypto.PublicKey
		err := currentPublicKey.Unmarshal(val.ConsumerPublicKey)
		if err != nil {
			// this should never happen and is not recoverable because without the public key
			// we cannot generate a validator update to remove this validator
			panic(fmt.Errorf("could not unmarshall public key (%s): %w", val.ConsumerPublicKey, err))
		}

		validator, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, val.ProviderConsAddr)
		if !found {
			// This should never happen because when `val` was added as an opt-in validator it was bonded
			// and for it not to be found it means that it fully unbonded after an unbonding period. Assuming
			// an epoch is smaller than the unbonding period, we would have already removed this validator from
			// an opted-in validator. In any case, we can still recover in this case by sending a 0-power update.
			k.Logger(ctx).Error("validator with consensus address (%s) could not be found", val.ProviderConsAddr)
			//updates = append(updates, abci.ValidatorUpdate{PubKey: currentPublicKey, Power: 0})
			continue
		}

		nextPower := k.stakingKeeper.GetLastValidatorPower(ctx, validator.GetOperator())

		// for a validator that just opts in, we can immediately use the next key
		nextPublicKey, found := k.GetValidatorConsumerPubKey(ctx, chainID, types.NewProviderConsAddress(val.ProviderConsAddr))
		if !found {
			var err error
			nextPublicKey, err = validator.TmConsPublicKey()
			if err != nil {
				k.Logger(ctx).Error("could not retrieve public key from validator (%s)", val.ProviderConsAddr)
				continue
			}
		}

		nextPublicKeyBytes, err := nextPublicKey.Marshal()

		k := types.CurrentEpochOptedInValidator{
			ProviderConsAddr:  val.ProviderConsAddr,
			StartBlockHeight:  ctx.BlockHeight(),
			Power:             nextPower,
			ConsumerPublicKey: nextPublicKeyBytes,
		}
		val.Power = nextPower
		val.ConsumerPublicKey = nextPublicKeyBytes

		// validator `val` was not removed, so it would still be part of the next opted-in validators
		nextValidators = append(nextValidators, k)
	}

	return nextValidators
}

// rename to EpochValidator ... because not opted i yet ... no?
func (k Keeper) diff(
	currentValidators []types.CurrentEpochOptedInValidator,
	nextValidators []types.CurrentEpochOptedInValidator) []abci.ValidatorUpdate {
	var updates []abci.ValidatorUpdate
	isCurrentValidator := make(map[string]types.CurrentEpochOptedInValidator)
	for _, val := range currentValidators {
		isCurrentValidator[string(val.ProviderConsAddr)] = val
	}

	isNextValidator := make(map[string]types.CurrentEpochOptedInValidator)
	for _, val := range nextValidators {
		isNextValidator[string(val.ProviderConsAddr)] = val
	}

	for _, val := range currentValidators {
		if nextVal, found := isNextValidator[string(val.ProviderConsAddr)]; found {
			// validator remains in the next epoch
			var currentPublicKey crypto.PublicKey
			err := currentPublicKey.Unmarshal(val.ConsumerPublicKey)
			// unrecoverable error
			if err != nil {
				panic("")
			}

			var nextPublicKey crypto.PublicKey
			err = nextPublicKey.Unmarshal(nextVal.ConsumerPublicKey)
			if err != nil {
				panic("...")
			}

			if !currentPublicKey.Equal(nextPublicKey) {
				updates = append(updates, abci.ValidatorUpdate{PubKey: currentPublicKey, Power: 0})
			}
			updates = append(updates, abci.ValidatorUpdate{PubKey: nextPublicKey, Power: nextVal.Power})
		} else {
			// not found in next validators and hence the validator has to be removed
			var currentPublicKey crypto.PublicKey
			err := currentPublicKey.Unmarshal(val.ConsumerPublicKey)
			if err != nil {
				panic("..")
			}

			updates = append(updates, abci.ValidatorUpdate{PubKey: currentPublicKey, Power: 0})
		}
	}

	// validators to be added
	for _, val := range nextValidators {
		if nextVal, found := isCurrentValidator[string(val.ProviderConsAddr)]; !found {
			var nextPublicKey crypto.PublicKey
			err := nextPublicKey.Unmarshal(nextVal.ConsumerPublicKey)
			if err != nil {
				panic("..")
			}

			updates = append(updates, abci.ValidatorUpdate{PubKey: nextPublicKey, Power: nextVal.Power})
		}
	}

	return updates
}

// ResetCurrentEpochOptedInValidators resets the opted-in validators with the newest set that was computed by
// `ComputeNextValidators` and hence this method should only be called after `ComputeNextValidators` has completed.
func (k Keeper) ResetCurrentEpochOptedInValidators(ctx sdk.Context, chainID string,
	nextValidators []types.CurrentEpochOptedInValidator) {
	k.DeleteAllOptedIn(ctx, chainID)
	for _, val := range nextValidators {
		k.SetOptedIn(ctx, chainID, val)
	}
}
