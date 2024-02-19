package keeper

import (
	errorsmod "cosmossdk.io/errors"
	"fmt"
	abci "github.com/cometbft/cometbft/abci/types"
	"github.com/cometbft/cometbft/proto/tendermint/crypto"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
)

func (k Keeper) HandleOptIn(ctx sdk.Context, chainID string, providerAddr types.ProviderConsAddress, consumerKey *string) error {
	if !k.IsConsumerProposedOrRegistered(ctx, chainID) {
		return errorsmod.Wrapf(
			types.ErrUnknownConsumerChainId,
			"opting in to an unknown consumer chain, with id: %s", chainID)
	}

	validator, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, providerAddr.ToSdkConsAddr())
	if !found {
		return errorsmod.Wrapf(
			types.ErrNoValidatorProviderAddress,
			"could not find validator with consensus address: %s", providerAddr.ToSdkConsAddr().Bytes())
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

		err = k.AssignConsumerKey(ctx, chainID, validator, consumerTMPublicKey)
		if err != nil {
			return err
		}
	}

	return nil
}

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

// ComputeValidatorUpdatesAndNextValidators returns the validator updates needed to be sent to the consumer chain to
// capture the newly opted-in and opted-out validators, as well as validators that unbonded. It also computes the
// next validator set that is responsible for validating on a consumer chain.
func (k Keeper) ComputeValidatorUpdatesAndNextValidators(ctx sdk.Context,
	chainID string,
	currentValidators []types.OptedInValidator,
	validatorAddressesToAdd []types.ProviderConsAddress,
	validatorAddressesToRemove []types.ProviderConsAddress,
) (updates []abci.ValidatorUpdate, nextValidators []types.OptedInValidator) {
	// store in a map all the validators that are to be removed, so we can filter out those
	// validators when we go through `currentValidators`
	isRemoved := make(map[string]bool)
	for _, addr := range validatorAddressesToRemove {
		isRemoved[addr.String()] = true
	}

	// go through all opted-in validators and look in the following order:
	// - if the validator has opted out, generate a 0-power update
	// - if the validator is not bonded anymore, generate a 0-power update
	// - if the validator has changed its consumer key since last epoch, generate a 0-power update for the old key
	//   and generate an update with the new power and the new key
	// - if the validator has not changed its consumer key but has changed its voting power since last epoch,
	//   generate an update with the new power
	// - if validator has not changed its consumer key or its voting power since, then do not generate an update
	for _, val := range currentValidators {
		// `currentPublicKey` is the currently used key by validator `val` when validating on the consumer chain
		var currentPublicKey crypto.PublicKey
		err := currentPublicKey.Unmarshal(val.PublicKey)
		if err != nil {
			// this should never happen and is not recoverable because without the public key
			// we cannot generate a validator update to remove this validator
			panic(fmt.Errorf("could not unmarshall public key (%s): %w", val.PublicKey, err))
		}

		providerAddr := types.NewProviderConsAddress(val.ProviderAddr)
		if isRemoved[providerAddr.String()] {
			// if the validator is removed, then generate a 0-power update to remove
			// validator `val` from the consumer chain
			updates = append(updates, abci.ValidatorUpdate{PubKey: currentPublicKey, Power: 0})
			continue
		}

		validator, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, val.ProviderAddr)
		if !found {
			// This should never happen because when `val` was added as an opt-in validator it was bonded
			// and for it not to be found it means that it fully unbonded after an unbonding period. Assuming
			// an epoch is smaller than the unbonding period, we would have already removed this validator from
			// an opted-in validator. In any case, we can still recover in this case by sending a 0-power update.
			k.Logger(ctx).Error("validator with consensus address (%s) could not be found", val.ProviderAddr)
			updates = append(updates, abci.ValidatorUpdate{PubKey: currentPublicKey, Power: 0})
			continue
		}

		nextPower := k.stakingKeeper.GetLastValidatorPower(ctx, validator.GetOperator())
		if nextPower == 0 {
			// if the validator is not bonded anymore, then send an update with 0 power to remove validator
			updates = append(updates, abci.ValidatorUpdate{PubKey: currentPublicKey, Power: 0})
			continue
		}

		// get the consumer key the validator intends to use to validate on the consumer chain
		nextPublicKey, found := k.GetValidatorConsumerPubKey(ctx, chainID, types.NewProviderConsAddress(val.ProviderAddr))
		if !found {
			// if not found, then the current consumer key is the same
			// as the one the validator used when it first opted in
			nextPublicKey = currentPublicKey
		}

		if !nextPublicKey.Equal(currentPublicKey) {
			// if the validator has changed its consumer key since last it opted in, then generate a 0-power update
			// for the old consumer key, and an update with the new key with the new power
			updates = append(updates, abci.ValidatorUpdate{PubKey: currentPublicKey, Power: 0})
			updates = append(updates, abci.ValidatorUpdate{PubKey: nextPublicKey, Power: nextPower})
		} else if val.Power != nextPower {
			// otherwise, only send an update if the power has changed since the last epoch
			updates = append(updates, abci.ValidatorUpdate{PubKey: nextPublicKey, Power: nextPower})
		}

		// update validator with the new power the validator has
		// at the end of this epoch and with the new key
		val.Power = nextPower
		val.PublicKey, err = nextPublicKey.Marshal()
		if err != nil {
			// this should never happen and would lead to `panic` later on when we try to `Unmarshal` the key
			panic(fmt.Errorf("could not marshal public key (%s): %w", nextPublicKey, err))
		}

		// validator `val` was not removed, so it would still be part of the next opted-in validators
		nextValidators = append(nextValidators, val)
	}

	// go through all to-be-opted-in validators and look in the following order:
	// - if the validator is not in the active set, do not generate an update for it
	for _, addr := range validatorAddressesToAdd {
		validator, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, addr.ToSdkConsAddr())
		if !found {
			k.Logger(ctx).Info("validator (%s) that was to-be-opted-in cannot be found anymore", addr)
			continue
		}

		if !validator.IsBonded() {
			// if the validator is not bonded anymore and hence not in the active set we do not add it
			continue
		}

		// for a validator that just opts in, we can immediately use the next key
		nextPublicKey, found := k.GetValidatorConsumerPubKey(ctx, chainID, addr)
		if !found {
			var err error
			nextPublicKey, err = validator.TmConsPublicKey()
			if err != nil {
				k.Logger(ctx).Error("could not retrieve public key from validator (%s)", addr)
				continue
			}
		}

		// for a validator that just opts in, we can immediately use the next power
		nextPower := k.stakingKeeper.GetLastValidatorPower(ctx, validator.GetOperator())
		updates = append(updates, abci.ValidatorUpdate{PubKey: nextPublicKey, Power: nextPower})

		nextPublicKeyBytes, err := nextPublicKey.Marshal()
		if err != nil {
			// this should never happen and would lead to `panic` later on when we try to `Unmarshal` the key
			panic(fmt.Errorf("could not marshal public key (%s): %w", nextPublicKey, err))
		}

		nextValidators = append(nextValidators,
			types.OptedInValidator{
				ProviderAddr: addr.ToSdkConsAddr(),
				BlockHeight:  ctx.BlockHeight(),
				// validator that just opted-in would be using next power and next key for the upcoming epoch
				Power:     nextPower,
				PublicKey: nextPublicKeyBytes,
			})
	}

	return updates, nextValidators
}

// ResetCurrentValidators resets the opted-in validators with the newest set that was computed by
// `ComputeNextValidators` and hence this method should only be called after
// `ComputeNextValidators` has completed. Method also clears all the `ToBeOptedIn` and `ToBeOptedOut` states.
func (k Keeper) ResetCurrentValidators(ctx sdk.Context, chainID string, nextValidators []types.OptedInValidator) {
	k.DeleteAllOptedIn(ctx, chainID)
	for _, val := range nextValidators {
		k.SetOptedIn(ctx, chainID, val)
	}

	k.DeleteAllToBeOptedIn(ctx, chainID)
	k.DeleteAllToBeOptedOut(ctx, chainID)
}
