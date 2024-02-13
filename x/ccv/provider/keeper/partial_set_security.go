package keeper

import (
	errorsmod "cosmossdk.io/errors"
	abci "github.com/cometbft/cometbft/abci/types"
	tmprotocrypto "github.com/cometbft/cometbft/proto/tendermint/crypto"
	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	"github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
)

type OptedInValidator struct {
	ProviderAddr types.ProviderConsAddress
	// block height the validator opted in at
	BlockHeight uint64
}

func (k Keeper) HandleOptIn(ctx sdk.Context, chainID string, providerAddr types.ProviderConsAddress, consumerKey *string) error {
	if !k.IsConsumerProposedOrRegistered(ctx, chainID) {
		return errorsmod.Wrapf(
			types.ErrUnknownConsumerChainId,
			"opting in to an unknown consumer chain, with id: %s", chainID)
	}

	val, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, providerAddr.ToSdkConsAddr())
	if !found {
		return errorsmod.Wrapf(
			types.ErrNoValidatorProviderAddress,
			"could not find validator with consensus address: %s", providerAddr.ToSdkConsAddr().Bytes())
	} else if !val.IsBonded() {
		// FIXME: problematic ...
		// Only active validators are allowed to opt in. Note that the fact that a validator is bonded when sending
		// a `MsgOptIn` message does not guarantee that the validator would still be bonded when the validator actually
		// opts in (e.g., at the end of a block or of an epoch). We recheck if validators are bonded in
		// `GetToBeOptedInValidatorUpdates` before sending the partial set to a consumer chain.
		return errorsmod.Wrapf(
			types.ErrValidatorNotBonded,
			"validator with consensus address: %s is not bonded", providerAddr.ToSdkConsAddr().Bytes())
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

func (k Keeper) getValidatorsPublicKey(validator stakingtypes.Validator) (tmprotocrypto.PublicKey, error) {
	consAddr, err := validator.GetConsAddr()
	if err != nil {
		return tmprotocrypto.PublicKey{}, err
	}
	return tmprotocrypto.PublicKey{
		Sum: &tmprotocrypto.PublicKey_Ed25519{
			Ed25519: consAddr.Bytes(),
		},
	}, nil
}

// GetToBeOptedInValidatorUpdates returns all the needed `ValidatorUpdate`s for validators that are to be opted in
// on consumer chain with `chainID`
func (k Keeper) GetToBeOptedInValidatorUpdates(ctx sdk.Context, chainID string) []abci.ValidatorUpdate {
	var updates []abci.ValidatorUpdate
	for _, val := range k.GetToBeOptedIn(ctx, chainID) {
		validator, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, val.ToSdkConsAddr())
		if !found {
			// a validator was successfully set to be opted in, but we cannot find this validator anymore
			k.Logger(ctx).Error("could not find validator with consensus address: %s", val.ToSdkConsAddr().Bytes())
		}

		// FIXME: bonded means in the active ...
		if !validator.IsBonded() {
			// a validator might have started unbonding or unbonded since it asked to be opted in
			continue
		}

		pubKey, err := k.getValidatorsPublicKey(validator)
		if err != nil {
			k.Logger(ctx).Error("could not find validator with consensus address: %s", val.ToSdkConsAddr().Bytes())
			continue
		}

		updates = append(updates, abci.ValidatorUpdate{
			PubKey: pubKey,
			Power:  k.stakingKeeper.GetLastValidatorPower(ctx, validator.GetOperator()),
		})
	}

	return updates
}

// GetToBeOptedOutValidatorUpdates returns all the needed `ValidatorUpdate`s for validators that are to be opted out
// of the consumer chain with `chainID`
func (k Keeper) GetToBeOptedOutValidatorUpdates(ctx sdk.Context, chainID string) []abci.ValidatorUpdate {
	var updates []abci.ValidatorUpdate
	for _, val := range k.GetToBeOptedOut(ctx, chainID) {
		validator, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, val.ToSdkConsAddr())
		if !found {
			// a validator was successfully set to be opted in, but we cannot find this validator anymore
			k.Logger(ctx).Error("could not find validator with consensus address: %s", val.ToSdkConsAddr().Bytes())
			continue
		}

		pubKey, err := k.getValidatorsPublicKey(validator)
		if err != nil {
			continue
		}

		updates = append(updates, abci.ValidatorUpdate{
			PubKey: pubKey,
			Power:  0,
		})
	}
	return updates
}

// ComputePartialSetValUpdates computes and returns the partial set `ValidatorUpdate`s for given chain with `chainID`
// and provided the `stakingUpdates` stemming from the staking module
func (k Keeper) ComputePartialSetValUpdates(ctx sdk.Context, chainID string, stakingUpdates []abci.ValidatorUpdate) []abci.ValidatorUpdate {
	var partialSetUpdates []abci.ValidatorUpdate

	toBeOptedInValidatorUpdates := k.GetToBeOptedInValidatorUpdates(ctx, chainID)
	toBeOptedOutValidatorUpdates := k.GetToBeOptedOutValidatorUpdates(ctx, chainID)

	partialSetUpdates = append(partialSetUpdates, toBeOptedInValidatorUpdates...)
	partialSetUpdates = append(partialSetUpdates, toBeOptedOutValidatorUpdates...)

	// Create set that contains all the validators that are to be opted out so that we do not reintroduce opted-out
	// validators when going through the already opted in validators. Opted out validators are already included
	// in the partial set updates through `toBeOptedOutValidatorUpdates`.
	isSetToBeOptedOut := make(map[string]bool)
	for _, val := range toBeOptedOutValidatorUpdates {
		isSetToBeOptedOut[val.PubKey.String()] = true
	}

	// Create set that contains all the validators that stem from `stakingUpdates` changes so that we only send
	// validator updates for validators that had a change in their voting power.
	isStakingUpdate := make(map[string]bool)
	for _, val := range stakingUpdates {
		isStakingUpdate[val.PubKey.String()] = true
	}

	for _, val := range k.GetOptedIn(ctx, chainID) {
		validator, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, val.ProviderAddr.ToSdkConsAddr())
		if !found {
			continue
		}
		pubKey, err := k.getValidatorsPublicKey(validator)
		if err != nil {
			continue
		}

		if isSetToBeOptedOut[pubKey.String()] {
			// do not create a `ValidatorUpdate` for validators that opt out
			continue
		}

		if !isStakingUpdate[pubKey.String()] {
			// only send an update if an opted in validator had a staking update from the staking module and
			// hence a voting power change
			continue
		}

		partialSetUpdates = append(partialSetUpdates, abci.ValidatorUpdate{
			PubKey: pubKey,
			Power:  k.stakingKeeper.GetLastValidatorPower(ctx, validator.GetOperator()),
		})
	}

	return partialSetUpdates
}

func (k Keeper) ResetPartialSet(ctx sdk.Context, chainID string) {
	var optedOutOnes map[string]bool
	for _, v := range k.GetToBeOptedIn(ctx, chainID) {
		optedOutOnes[v.String()] = true
	}

	var allOfThem []types.ProviderConsAddress
	for _, v := range k.GetOptedIn(ctx, chainID) {
		// FOXME:
		validator, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, v.ProviderAddr.ToSdkConsAddr())
		if !found {
			// probably an error
			continue
		}
		if !validator.IsBonded() {
			continue
		}
		// only still bonded ones ...
		if optedOutOnes[v.ProviderAddr.String()] {
			// here you would need ot remove
			continue
		}
		allOfThem = append(allOfThem, v.ProviderAddr)
	}

	for _, v := range k.GetToBeOptedIn(ctx, chainID) {
		// only still bonded ones ...
		validator, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, v.ToSdkConsAddr())
		if !found {
			// probably an error
			continue
		}
		if !validator.IsBonded() {
			continue
		}
		allOfThem = append(allOfThem, types.NewProviderConsAddress(v.Address))
	}

	for _, v := range allOfThem {
		if !k.IsOptedIn(ctx, chainID, v) {
			k.SetOptedIn(ctx, chainID, v, uint64(ctx.BlockHeight()))
		} else {
			// leave the previous block height as is
		}
	}

	k.DeleteAllToBeOptedIn(ctx, chainID)
	k.DeleteAllToBeOptedOut(ctx, chainID)
}
