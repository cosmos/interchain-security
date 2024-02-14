package keeper

import (
	errorsmod "cosmossdk.io/errors"
	abci "github.com/cometbft/cometbft/abci/types"
	tmprotocrypto "github.com/cometbft/cometbft/proto/tendermint/crypto"
	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	"github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
	"sort"
)

type OptedInValidator struct {
	ProviderAddr types.ProviderConsAddress
	// block height the validator opted in at
	BlockHeight uint64
	// power the validator had when it opted in
	Power uint64
}

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

// getValidatorsPublicKey is a helper function that returns the public key of the validator
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

// getValidatorOperatorAddressAndPublicKey is a helper function that returns the public key of the validator
func (k Keeper) getValidatorOperatorAddressAndPublicKey(ctx sdk.Context, addr types.ProviderConsAddress) (sdk.ValAddress, tmprotocrypto.PublicKey, error) {
	validator, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, addr.ToSdkConsAddr())
	if !found {

	}
	consAddr, err := validator.GetConsAddr()
	if err != nil {
		return sdk.ValAddress{}, tmprotocrypto.PublicKey{}, err
	}

	pubKey := tmprotocrypto.PublicKey{
		Sum: &tmprotocrypto.PublicKey_Ed25519{
			Ed25519: consAddr.Bytes(),
		},
	}
	return validator.GetOperator(), pubKey, nil
}

//func filterAddresses(addresses []types.ProviderConsAddress, predicate func(types.ProviderConsAddress) bool) []types.ProviderConsAddress {
//	var filteredAddresses []types.ProviderConsAddress
//	for _, addr := range addresses {
//		if predicate(addr) {
//			filteredAddresses = append(filteredAddresses, addr)
//		}
//	}
//	return filteredAddresses
//}
//
//func filterOptedInValidators(addresses []OptedInValidator, predicate func(validator OptedInValidator) bool) []OptedInValidator {
//	var filteredAddresses []OptedInValidator
//	for _, addr := range addresses {
//		if predicate(addr) {
//			filteredAddresses = append(filteredAddresses, addr)
//		}
//	}
//	return filteredAddresses
//}

//// GetBondedToBeOptedInValidators returns all the bonded validators that are to be opted in
//// on consumer chain with `chainID`
//func (k Keeper) GetBondedToBeOptedInValidators(ctx sdk.Context, chainID string) []types.ProviderConsAddress {
//	var consAddresses []types.ProviderConsAddress
//
//	bondedToBeOptedInValidators :=
//		filterAddresses(k.GetToBeOptedIn(ctx, chainID), func(addr types.ProviderConsAddress) bool {
//			validator, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, addr.ToSdkConsAddr())
//			if !found {
//				// a validator was successfully set to be opted in, but we cannot find this validator anymore
//				k.Logger(ctx).Error("could not find to-be-opted-in invalidator with consensus address: %s", addr.ToSdkConsAddr().Bytes())
//				return false
//			}
//
//			if !validator.IsBonded() {
//				// only consider validators that are in the active set
//				return false
//			}
//			return true
//		})
//
//	return bondedToBeOptedInValidators
//
//	//for _, addr := range k.GetToBeOptedIn(ctx, chainID) {
//	//	validator, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, addr.ToSdkConsAddr())
//	//	if !found {
//	//		// a validator was successfully set to be opted in, but we cannot find this validator anymore
//	//		k.Logger(ctx).Error("could not find to-be-opted-in invalidator with consensus address: %s", addr.ToSdkConsAddr().Bytes())
//	//		continue
//	//	}
//	//
//	//	if !validator.IsBonded() {
//	//		// only consider validators that are in the active set
//	//		continue
//	//	}
//	//	consAddresses = append(consAddresses, addr)
//	//}
//
//	return consAddresses
//}

//// GetOptedInValidatorsForValUpdates returns all the addresses of validators that are going to be opted in
//// next on the consumer chain with `chainID` and a validator update would need to be sent for them
//func (k Keeper) GetOptedInValidatorsForValUpdates(ctx sdk.Context, chainID string) []types.ProviderConsAddress {
//	var consAddresses []types.ProviderConsAddress
//
//	// Create set that contains all the validators that are to be opted out so that we do not reintroduce opted-out
//	// validators when going through the already opted in validators.
//	isSetToBeOptedOut := make(map[string]bool)
//	for _, addr := range k.GetToBeOptedOut(ctx, chainID) {
//		isSetToBeOptedOut[addr.ToSdkConsAddr().String()] = true
//	}
//
//	for _, val := range k.GetOptedIn(ctx, chainID) {
//		// go through all the validators that are currently opted in
//		validator, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, val.ProviderAddr.ToSdkConsAddr())
//		if !found {
//			// a validator was opted in, but we cannot find this validator anymore
//			k.Logger(ctx).Error("could not find opted-in validator with consensus address: %s",
//				val.ProviderAddr.ToSdkConsAddr().Bytes())
//			continue
//		}
//
//		if isSetToBeOptedOut[val.ProviderAddr.ToSdkConsAddr().String()] {
//			continue
//		}
//
//		if val.Power == uint64(k.stakingKeeper.GetLastValidatorPower(ctx, validator.GetOperator())) {
//			// Only send an update if an opted-in validator had a power change since the lat time it was sent.
//			// If an opted-in validator is not in the active set anymore, then its new power is 0 and hence we
//			// do not consider this validator in the next set of opted in validators.
//			continue
//		}
//
//		consAddresses = append(consAddresses, val.ProviderAddr)
//	}
//
//	// append all the to-be-opted-in validators
//	consAddresses = append(consAddresses, k.GetBondedToBeOptedInValidators(ctx, chainID)...)
//	return consAddresses
//}

//// ComputePartialSetValidatorUpdates returns the partial set of `ValidatorUpdate`s that the provider chain sends to the
//// consumer chain. Receives `nextOptedIn` that corresponds to the validators that would be opted in next and
//// `toBeOptedOut` that contains the validators that would be opted out.
//func (k Keeper) ComputePartialSetValidatorUpdates(ctx sdk.Context, optedInValidatorsForValUpdates []types.ProviderConsAddress,
//	toBeOptedOut []types.ProviderConsAddress) []abci.ValidatorUpdate {
//	var partialSetUpdates []abci.ValidatorUpdate
//
//	for _, val := range optedInValidatorsForValUpdates {
//		validator, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, val.ToSdkConsAddr())
//		if !found {
//			// any validator in `optedInValidatorsForValUpdates` should be found
//			k.Logger(ctx).Error("could not find validator with consensus address: %s",
//				val.ToSdkConsAddr().Bytes())
//			continue
//		}
//
//		pubKey, err := k.getValidatorsPublicKey(validator)
//		if err != nil {
//			k.Logger(ctx).Error("could retrieve public key from validator with consensus address: %s",
//				val.ToSdkConsAddr().Bytes())
//			continue
//		}
//
//		// if a validator that was opted in, is not in the active set anymore, then `GetLastValidatorPower` returns 0
//		partialSetUpdates = append(partialSetUpdates, abci.ValidatorUpdate{
//			PubKey: pubKey,
//			Power:  k.stakingKeeper.GetLastValidatorPower(ctx, validator.GetOperator()),
//		})
//	}
//
//	for _, addr := range toBeOptedOut {
//		// go through all the validators that are currently opted in
//		validator, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, addr.ToSdkConsAddr())
//		if !found {
//			// a validator was opted in, but we cannot find this validator anymore
//			k.Logger(ctx).Error("could not find opted-in validator with consensus address: %s",
//				addr.ToSdkConsAddr().Bytes())
//			continue
//		}
//		pubKey, err := k.getValidatorsPublicKey(validator)
//		if err != nil {
//			k.Logger(ctx).Error("could retrieve public key from validator with consensus address: %s",
//				addr.ToSdkConsAddr().Bytes())
//			continue
//		}
//
//		// send power 0 so the validator is removed
//		partialSetUpdates = append(partialSetUpdates, abci.ValidatorUpdate{
//			PubKey: pubKey,
//			Power:  0,
//		})
//	}
//
//	return partialSetUpdates
//}

func (k Keeper) ComputeNextValidators(ctx sdk.Context, currentValidators []OptedInValidator,
	validatorsToAdd []types.ProviderConsAddress,
	validatorsToRemove []types.ProviderConsAddress,
) []OptedInValidator {
	isRemoved := make(map[string]bool)
	for _, val := range validatorsToRemove {
		isRemoved[val.ToSdkConsAddr().String()] = true
	}

	var out []OptedInValidator
	for _, val := range currentValidators {
		if isRemoved[val.ProviderAddr.ToSdkConsAddr().String()] {
			continue
		}
		valAddress, _, err := k.getValidatorOperatorAddressAndPublicKey(ctx, val.ProviderAddr)
		if err != nil {
			// FIXME
			continue
		}

		val.Power = uint64(k.stakingKeeper.GetLastValidatorPower(ctx, valAddress))
		if val.Power == 0 {
			continue
		}
		out = append(out, val)
	}

	for _, addr := range validatorsToAdd {
		valAddress, _, err := k.getValidatorOperatorAddressAndPublicKey(ctx, addr)
		if err != nil {
			// FIXME
			continue
		}

		validator, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, addr.ToSdkConsAddr())
		if !found {
			continue
		}
		if !validator.IsBonded() {
			continue
		}
		power := uint64(k.stakingKeeper.GetLastValidatorPower(ctx, valAddress))

		out = append(out, OptedInValidator{ProviderAddr: addr, BlockHeight: uint64(ctx.BlockHeight()), Power: power})
	}

	return out
}

func (k Keeper) ComputeValidatorUpdates(ctx sdk.Context,
	currentValidators []OptedInValidator,
	validatorsToAdd []types.ProviderConsAddress,
	validatorsToRemove []types.ProviderConsAddress,
) []abci.ValidatorUpdate {
	var m = make(map[string]abci.ValidatorUpdate)

	for _, val := range currentValidators {
		valAddress, pubKey, err := k.getValidatorOperatorAddressAndPublicKey(ctx, val.ProviderAddr)
		if err != nil {
			// FIXME ...
		}

		validator, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, val.ProviderAddr.ToSdkConsAddr())
		if !found {
			continue
		}

		if val.Power == uint64(k.stakingKeeper.GetLastValidatorPower(ctx, validator.GetOperator())) {
			continue
		}

		// if this validator has unbonded, the result would be 0 of power so we still good!! but then if you add, you readd
		// no, because we check if bonded when we readd ... you cannot readd if already here
		m[pubKey.String()] = abci.ValidatorUpdate{
			PubKey: pubKey,
			Power:  k.stakingKeeper.GetLastValidatorPower(ctx, valAddress),
		}
	}

	for _, addr := range validatorsToAdd {
		valAddress, pubKey, err := k.getValidatorOperatorAddressAndPublicKey(ctx, addr)
		if err != nil {

		}

		validator, found := k.stakingKeeper.GetValidatorByConsAddr(ctx, addr.ToSdkConsAddr())
		if !found {
			continue
		}
		if !validator.IsBonded() {
			continue
		}

		m[pubKey.String()] = abci.ValidatorUpdate{
			PubKey: pubKey,
			Power:  k.stakingKeeper.GetLastValidatorPower(ctx, valAddress),
		}
	}

	for _, addr := range validatorsToRemove {
		_, pubKey, err := k.getValidatorOperatorAddressAndPublicKey(ctx, addr)
		if err != nil {

		}

		m[pubKey.String()] = abci.ValidatorUpdate{
			PubKey: pubKey,
			Power:  0,
		}

	}

	var out []abci.ValidatorUpdate
	for _, update := range m {
		out = append(out, update)
	}

	// similar to `AccumulateChanges`
	// The list of tendermint updates should hash the same across all consensus nodes
	// that means it is necessary to sort for determinism.
	sort.Slice(out, func(i, j int) bool {
		if out[i].Power != out[j].Power {
			return out[i].Power > out[j].Power
		}
		return out[i].PubKey.String() > out[j].PubKey.String()
	})

	return out
}

// ResetCurrentValidators resets the opted-in validators with the newest set that was computed by
// `ComputePartialSetValidatorUpdates` and hence this method should only be called  after
// `ComputePartialSetValidatorUpdates` has complete. Also, clears all the `ToBeOptedIn` and `ToBeOptedOut` sets.
func (k Keeper) ResetCurrentValidators(ctx sdk.Context, chainID string, nextValidators []OptedInValidator) {
	k.DeleteAllOptedIn(ctx, chainID)
	for _, val := range nextValidators {
		k.SetOptedIn(ctx, chainID, val.ProviderAddr, val.BlockHeight, val.Power)
	}

	k.DeleteAllToBeOptedIn(ctx, chainID)
	k.DeleteAllToBeOptedOut(ctx, chainID)
}
