package keeper

import (
	"encoding/base64"
	"fmt"
	"time"

	errorsmod "cosmossdk.io/errors"
	storetypes "cosmossdk.io/store/types"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	tmprotocrypto "github.com/cometbft/cometbft/proto/tendermint/crypto"

	"github.com/cosmos/interchain-security/v6/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v6/x/ccv/types"
)

// ParseConsumerKey parses the ED25519 PubKey`consumerKey` from a JSON string
// and constructs its corresponding `tmprotocrypto.PublicKey`
func (k Keeper) ParseConsumerKey(consumerKey string) (tmprotocrypto.PublicKey, error) {
	// parse consumer key as long as it's in the right format
	pkType, keyStr, err := types.ParseConsumerKeyFromJson(consumerKey)
	if err != nil {
		return tmprotocrypto.PublicKey{}, err
	}

	// Note: the correct way to decide if a key type is supported is to check the
	// consensus params. However this functionality was disabled in https://github.com/cosmos/interchain-security/pull/916
	// as a quick way to get ed25519 working, avoiding amino/proto-any marshalling issues.

	// make sure the consumer key type is supported
	// cp := ctx.ConsensusParams()
	// if cp != nil && cp.Validator != nil {
	// 	if !tmstrings.StringInSlice(pkType, cp.Validator.PubKeyTypes) {
	// 		return nil, errorsmod.Wrapf(
	// 			stakingtypes.ErrValidatorPubKeyTypeNotSupported,
	// 			"got: %s, expected one of: %s", pkType, cp.Validator.PubKeyTypes,
	// 		)
	// 	}
	// }

	// For now, only accept ed25519.
	// TODO: decide what types should be supported.
	if pkType != "/cosmos.crypto.ed25519.PubKey" {
		return tmprotocrypto.PublicKey{}, errorsmod.Wrapf(
			stakingtypes.ErrValidatorPubKeyTypeNotSupported,
			"got: %s, expected: %s", pkType, "/cosmos.crypto.ed25519.PubKey",
		)
	}

	pubKeyBytes, err := base64.StdEncoding.DecodeString(keyStr)
	if err != nil {
		return tmprotocrypto.PublicKey{}, err
	}

	consumerTMPublicKey := tmprotocrypto.PublicKey{
		Sum: &tmprotocrypto.PublicKey_Ed25519{
			Ed25519: pubKeyBytes,
		},
	}

	return consumerTMPublicKey, nil
}

// GetValidatorConsumerPubKey returns a validator's public key assigned for a consumer chain
func (k Keeper) GetValidatorConsumerPubKey(
	ctx sdk.Context,
	consumerId string,
	providerAddr types.ProviderConsAddress,
) (consumerKey tmprotocrypto.PublicKey, found bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerValidatorsKey(consumerId, providerAddr))
	if bz == nil {
		return consumerKey, false
	}
	err := consumerKey.Unmarshal(bz)
	if err != nil {
		// An error here would indicate something is very wrong,
		// the consumer key is assumed to be correctly serialized in SetValidatorConsumerPubKey.
		panic(fmt.Sprintf("failed to unmarshal consumer key: %v", err))
	}
	return consumerKey, true
}

// SetValidatorConsumerPubKey sets a validator's public key assigned for a consumer chain
func (k Keeper) SetValidatorConsumerPubKey(
	ctx sdk.Context,
	consumerId string,
	providerAddr types.ProviderConsAddress,
	consumerKey tmprotocrypto.PublicKey,
) {
	store := ctx.KVStore(k.storeKey)
	bz, err := consumerKey.Marshal()
	if err != nil {
		// An error here would indicate something is very wrong,
		// the consumer key is obtained from GetValidatorConsumerPubKey, called from
		panic(fmt.Sprintf("failed to marshal consumer key: %v", err))
	}
	store.Set(types.ConsumerValidatorsKey(consumerId, providerAddr), bz)
}

// GetAllValidatorConsumerPubKeys gets all the validators public keys assigned for a consumer chain
// If consumerId is nil, it returns all the validators public keys assigned for all consumer chains
//
// Note that the validators public keys assigned for a consumer chain are stored under keys
// with the following format: ConsumerValidatorsBytePrefix | len(consumerId) | consumerId | providerAddress
// Thus, the returned array is
//   - in ascending order of providerAddresses, if consumerId is not nil;
//   - in undetermined order, if consumerId is nil.
func (k Keeper) GetAllValidatorConsumerPubKeys(ctx sdk.Context, consumerId *string) (validatorConsumerPubKeys []types.ValidatorConsumerPubKey) {
	store := ctx.KVStore(k.storeKey)
	var prefix []byte
	consumerValidatorsKeyPrefix := types.ConsumerValidatorsKeyPrefix()
	if consumerId == nil {
		// iterate over the validators public keys assigned for all consumer chains
		prefix = []byte{consumerValidatorsKeyPrefix}
	} else {
		// iterate over the validators public keys assigned for consumerId
		prefix = types.StringIdWithLenKey(consumerValidatorsKeyPrefix, *consumerId)
	}
	iterator := storetypes.KVStorePrefixIterator(store, prefix)
	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		// TODO: store consumerId and provider cons address in value bytes, marshaled as protobuf type
		consumerId, providerAddrTmp, err := types.ParseStringIdAndConsAddrKey(consumerValidatorsKeyPrefix, iterator.Key())
		if err != nil {
			// An error here would indicate something is very wrong,
			// the store key is assumed to be correctly serialized in SetValidatorConsumerPubKey.
			panic(err)
		}
		providerAddr := types.NewProviderConsAddress(providerAddrTmp)
		var consumerKey tmprotocrypto.PublicKey
		err = consumerKey.Unmarshal(iterator.Value())
		if err != nil {
			// An error here would indicate something is very wrong,
			// the consumer key is assumed to be correctly serialized in SetValidatorConsumerPubKey.
			panic(fmt.Sprintf("failed to unmarshal consumer key: %v", err))
		}

		validatorConsumerPubKeys = append(validatorConsumerPubKeys, types.ValidatorConsumerPubKey{
			ChainId:      consumerId,
			ProviderAddr: providerAddr.ToSdkConsAddr(),
			ConsumerKey:  &consumerKey,
		})
	}

	return validatorConsumerPubKeys
}

// DeleteValidatorConsumerPubKey deletes a validator's public key assigned for a consumer chain
func (k Keeper) DeleteValidatorConsumerPubKey(ctx sdk.Context, consumerId string, providerAddr types.ProviderConsAddress) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerValidatorsKey(consumerId, providerAddr))
}

// GetValidatorByConsumerAddr returns a validator's consensus address on the provider
// given the validator's consensus address on a consumer
func (k Keeper) GetValidatorByConsumerAddr(
	ctx sdk.Context,
	consumerId string,
	consumerAddr types.ConsumerConsAddress,
) (providerAddr types.ProviderConsAddress, found bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ValidatorsByConsumerAddrKey(consumerId, consumerAddr))
	if bz == nil {
		return providerAddr, false
	}
	providerAddr = types.NewProviderConsAddress(bz)
	return providerAddr, true
}

// SetValidatorByConsumerAddr sets the mapping from a validator's consensus address on a consumer
// to the validator's consensus address on the provider
func (k Keeper) SetValidatorByConsumerAddr(
	ctx sdk.Context,
	consumerId string,
	consumerAddr types.ConsumerConsAddress,
	providerAddr types.ProviderConsAddress,
) {
	store := ctx.KVStore(k.storeKey)
	// Cons address is a type alias for a byte string, no marshaling needed
	bz := providerAddr.ToSdkConsAddr()
	store.Set(types.ValidatorsByConsumerAddrKey(consumerId, consumerAddr), bz)
}

// GetValidatorsByConsumerAddrs gets all the mappings from consensus addresses
// on a given consumer chain to consensus addresses on the provider chain.
// If consumerId is nil, it returns all the mappings from consensus addresses on all consumer chains.
//
// Note that the mappings for a consumer chain are stored under keys with the following format:
// ValidatorsByConsumerAddrKeyPrefix | len(consumerId) | consumerId | consumerAddress
// Thus, the returned array is
//   - in ascending order of consumerAddresses, if consumerId is not nil;
//   - in undetermined order, if consumerId is nil.
func (k Keeper) GetAllValidatorsByConsumerAddr(ctx sdk.Context, consumerId *string) (validatorConsumerAddrs []types.ValidatorByConsumerAddr) {
	store := ctx.KVStore(k.storeKey)
	var prefix []byte
	validatorsByConsumerAddrKeyPrefix := types.ValidatorsByConsumerAddrKeyPrefix()
	if consumerId == nil {
		// iterate over the mappings from consensus addresses on all consumer chains
		prefix = []byte{validatorsByConsumerAddrKeyPrefix}
	} else {
		// iterate over the mappings from consensus addresses on consumerId
		prefix = types.StringIdWithLenKey(validatorsByConsumerAddrKeyPrefix, *consumerId)
	}
	iterator := storetypes.KVStorePrefixIterator(store, prefix)
	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		// TODO: store consumerId and consumer cons address in value bytes, marshaled as protobuf type
		consumerId, consumerAddrTmp, err := types.ParseStringIdAndConsAddrKey(validatorsByConsumerAddrKeyPrefix, iterator.Key())
		if err != nil {
			// An error here would indicate something is very wrong,
			// store keys are assumed to be correctly serialized in SetValidatorByConsumerAddr.
			panic(fmt.Sprintf("failed to parse consumerId and consumer address: %v", err))
		}
		consumerAddr := types.NewConsumerConsAddress(consumerAddrTmp)
		providerAddr := types.NewProviderConsAddress(iterator.Value())

		validatorConsumerAddrs = append(validatorConsumerAddrs, types.ValidatorByConsumerAddr{
			ConsumerAddr: consumerAddr.ToSdkConsAddr(),
			ProviderAddr: providerAddr.ToSdkConsAddr(),
			ChainId:      consumerId,
		})
	}

	return validatorConsumerAddrs
}

// DeleteValidatorByConsumerAddr deletes the mapping from a validator's consensus address on a consumer
// to the validator's consensus address on the provider
func (k Keeper) DeleteValidatorByConsumerAddr(ctx sdk.Context, consumerId string, consumerAddr types.ConsumerConsAddress) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ValidatorsByConsumerAddrKey(consumerId, consumerAddr))
}

// AppendConsumerAddrsToPrune appends a consumer validator address to the list of consumer addresses
// that can be pruned once the block time is at least pruneTs.
//
// The following invariant needs to hold:
// For each consumer address cAddr in ValidatorByConsumerAddr,
//   - either there exists a provider address pAddr in ValidatorConsumerPubKey,
//     s.t. hash(ValidatorConsumerPubKey(pAddr)) = cAddr
//   - or there exists a timestamp in ConsumerAddrsToPrune s.t. cAddr in ConsumerAddrsToPrune(timestamp)
func (k Keeper) AppendConsumerAddrsToPrune(
	ctx sdk.Context,
	consumerId string,
	pruneTs time.Time,
	consumerAddr types.ConsumerConsAddress,
) {
	store := ctx.KVStore(k.storeKey)
	storeKey := types.ConsumerAddrsToPruneV2Key(consumerId, pruneTs)
	bz := store.Get(storeKey)
	var consumerAddrsToPrune types.AddressList
	if bz != nil {
		err := consumerAddrsToPrune.Unmarshal(bz)
		if err != nil {
			// An error here would indicate something is very wrong,
			// the data bytes are assumed to be correctly serialized by previous calls to this method.
			panic(err)
		}
	}
	consumerAddrsToPrune.Addresses = append(consumerAddrsToPrune.Addresses, consumerAddr.ToSdkConsAddr())
	bz, err := consumerAddrsToPrune.Marshal()
	if err != nil {
		// An error here would indicate something is very wrong,
		// consumerAddrsToPrune is instantiated in this method and should be able to be marshaled.
		panic(err)
	}
	store.Set(storeKey, bz)
}

// GetConsumerAddrsToPrune returns the list of consumer addresses to prune stored under timestamp ts.
// Note that this method is only used in testing.
func (k Keeper) GetConsumerAddrsToPrune(
	ctx sdk.Context,
	consumerId string,
	ts time.Time,
) (consumerAddrsToPrune types.AddressList) {
	store := ctx.KVStore(k.storeKey)

	bz := store.Get(types.ConsumerAddrsToPruneV2Key(consumerId, ts))
	if bz == nil {
		return
	}
	err := consumerAddrsToPrune.Unmarshal(bz)
	if err != nil {
		// An error here would indicate something is very wrong,
		// the list of consumer addresses is assumed to be correctly serialized in AppendConsumerAddrsToPrune.
		panic(fmt.Sprintf("failed to unmarshal consumer addresses to prune: %v", err))
	}
	return
}

// ConsumeConsumerAddrsToPrune returns the list of consumer addresses that can be pruned at timestamp ts.
// The returned addresses are removed from the store.
//
// Note that the list of all consumer addresses is stored under keys with the following format:
// ConsumerAddrsToPruneV2BytePrefix | len(consumerId) | consumerId | timestamp
// Thus, this method returns all the consumer addresses stored under keys in the following range:
// (ConsumerAddrsToPruneV2BytePrefix | len(consumerId) | consumerId | ts') where ts' <= ts
func (k Keeper) ConsumeConsumerAddrsToPrune(
	ctx sdk.Context,
	consumerId string,
	ts time.Time,
) (consumerAddrsToPrune types.AddressList) {
	store := ctx.KVStore(k.storeKey)
	consumerAddrsToPruneKeyPrefix := types.ConsumerAddrsToPruneV2KeyPrefix()
	startPrefix := types.StringIdWithLenKey(consumerAddrsToPruneKeyPrefix, consumerId)
	iterator := store.Iterator(startPrefix,
		storetypes.InclusiveEndBytes(types.ConsumerAddrsToPruneV2Key(consumerId, ts)))
	defer iterator.Close()

	var keysToDel [][]byte
	for ; iterator.Valid(); iterator.Next() {
		// Sanity check
		if _, pruneTs, err := types.ParseStringIdAndTsKey(consumerAddrsToPruneKeyPrefix, iterator.Key()); err != nil {
			// An error here would indicate something is very wrong,
			// store keys are assumed to be correctly serialized in AppendConsumerAddrsToPrune.
			k.Logger(ctx).Error("ParseStringIdAndTsKey failed",
				"key", string(iterator.Key()),
				"error", err.Error(),
			)
			continue
		} else if pruneTs.After(ts) {
			// An error here would indicate something is wrong the iterator
			k.Logger(ctx).Error("iterator in ConsumeConsumerAddrsToPrune failed", "key", string(iterator.Key()))
			continue
		}

		keysToDel = append(keysToDel, iterator.Key())

		var addrs types.AddressList
		if err := addrs.Unmarshal(iterator.Value()); err != nil {
			// An error here would indicate something is very wrong,
			// the list of consumer addresses is assumed to be correctly serialized in AppendConsumerAddrsToPrune.
			k.Logger(ctx).Error("unmarshaling in ConsumeConsumerAddrsToPrune failed",
				"key", string(iterator.Key()),
				"error", err.Error(),
			)
			continue
		}

		consumerAddrsToPrune.Addresses = append(consumerAddrsToPrune.Addresses, addrs.Addresses...)
	}

	for _, delKey := range keysToDel {
		store.Delete(delKey)
	}

	return consumerAddrsToPrune
}

// GetAllConsumerAddrsToPrune gets all consumer addresses that can be eventually pruned for a given consumerId.
//
// Note that the list of all consumer addresses is stored under keys with the following format:
// ConsumerAddrsToPruneV2BytePrefix | len(consumerId) | consumerId | timestamp
// Thus, the returned array is in ascending order of timestamps.
func (k Keeper) GetAllConsumerAddrsToPrune(ctx sdk.Context, consumerId string) (consumerAddrsToPrune []types.ConsumerAddrsToPruneV2) {
	store := ctx.KVStore(k.storeKey)
	consumerAddrsToPruneKeyPrefix := types.ConsumerAddrsToPruneV2KeyPrefix()
	iteratorPrefix := types.StringIdWithLenKey(consumerAddrsToPruneKeyPrefix, consumerId)
	iterator := storetypes.KVStorePrefixIterator(store, iteratorPrefix)
	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		_, ts, err := types.ParseStringIdAndTsKey(consumerAddrsToPruneKeyPrefix, iterator.Key())
		if err != nil {
			// An error here would indicate something is very wrong,
			// store keys are assumed to be correctly serialized in AppendConsumerAddrsToPrune.
			panic(err)
		}
		var addrs types.AddressList
		err = addrs.Unmarshal(iterator.Value())
		if err != nil {
			// An error here would indicate something is very wrong,
			// the list of consumer addresses is assumed to be correctly serialized in AppendConsumerAddrsToPrune.
			panic(err)
		}

		consumerAddrsToPrune = append(consumerAddrsToPrune, types.ConsumerAddrsToPruneV2{
			PruneTs:       ts,
			ConsumerAddrs: &addrs,
			ChainId:       consumerId,
		})
	}

	return consumerAddrsToPrune
}

// DeleteConsumerAddrsToPruneV2 deletes the list of consumer addresses mapped to a timestamp
func (k Keeper) DeleteConsumerAddrsToPrune(ctx sdk.Context, consumerId string, pruneTs time.Time) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerAddrsToPruneV2Key(consumerId, pruneTs))
}

// AssignConsumerKey assigns the consumerKey to the validator with providerAddr
// on the consumer chain with the given `consumerId`, if it is either registered or currently
// voted on in a ConsumerAddition governance proposal
func (k Keeper) AssignConsumerKey(
	ctx sdk.Context,
	consumerId string,
	validator stakingtypes.Validator,
	consumerKey tmprotocrypto.PublicKey,
) error {
	if !k.IsConsumerActive(ctx, consumerId) {
		// check that the consumer chain is either registered, initialized, or launched
		return errorsmod.Wrapf(
			types.ErrInvalidPhase,
			"cannot assign a key to a consumer chain that is not in the registered, initialized, or launched phase: %s", consumerId)
	}

	consAddrTmp, err := ccvtypes.TMCryptoPublicKeyToConsAddr(consumerKey)
	if err != nil {
		return err
	}
	consumerAddr := types.NewConsumerConsAddress(consAddrTmp)

	consAddrTmp, err = validator.GetConsAddr()
	if err != nil {
		return err
	}
	providerAddr := types.NewProviderConsAddress(consAddrTmp)

	if existingVal, err := k.stakingKeeper.GetValidatorByConsAddr(ctx, consumerAddr.ToSdkConsAddr()); err == nil {
		// If there is already a different validator using the consumer key to validate on the provider
		// we prevent assigning the consumer key.
		if existingVal.OperatorAddress != validator.OperatorAddress {
			return errorsmod.Wrapf(
				types.ErrConsumerKeyInUse, "a different validator already uses the consumer key",
			)
		}
		// We prevent a validator from assigning the default provider key as a consumer key
		// if it has not already assigned a different consumer key
		_, found := k.GetValidatorConsumerPubKey(ctx, consumerId, providerAddr)
		if !found {
			return errorsmod.Wrapf(
				types.ErrCannotAssignDefaultKeyAssignment,
				"a validator cannot assign the default key assignment unless its key on that consumer has already been assigned",
			)
		}
	}

	if _, found := k.GetValidatorByConsumerAddr(ctx, consumerId, consumerAddr); found {
		// This consumer key is already in use, or it is to be pruned. With this check we prevent another validator
		// from assigning the same consumer key as some other validator. Additionally, we prevent a validator from
		// reusing a consumer key that it used in the past and is now to be pruned.
		return errorsmod.Wrapf(
			types.ErrConsumerKeyInUse, "a validator has or had assigned this consumer key already",
		)
	}

	// get the previous key assigned for this validator on this consumer chain
	if oldConsumerKey, found := k.GetValidatorConsumerPubKey(ctx, consumerId, providerAddr); found {
		oldConsumerAddrTmp, err := ccvtypes.TMCryptoPublicKeyToConsAddr(oldConsumerKey)
		if err != nil {
			return err
		}
		oldConsumerAddr := types.NewConsumerConsAddress(oldConsumerAddrTmp)

		// check whether the consumer chain has already launched (i.e., a client to the consumer was already created)
		phase := k.GetConsumerPhase(ctx, consumerId)
		if phase == types.CONSUMER_PHASE_LAUNCHED {
			// mark the old consumer address as prunable once UnbondingPeriod elapses;
			// note: this state is removed on EndBlock
			unbondingPeriod, err := k.stakingKeeper.UnbondingTime(ctx)
			if err != nil {
				return err
			}
			k.AppendConsumerAddrsToPrune(
				ctx,
				consumerId,
				ctx.BlockTime().Add(unbondingPeriod),
				oldConsumerAddr,
			)
		} else {
			// if the consumer chain is not registered, then remove the mapping
			// from the old consumer address to the provider address
			k.DeleteValidatorByConsumerAddr(ctx, consumerId, oldConsumerAddr)
		}
	}

	// set the mapping from this validator's provider address to the new consumer key;
	// overwrite if already exists
	// note: this state is deleted when the validator is removed from the staking module
	k.SetValidatorConsumerPubKey(ctx, consumerId, providerAddr, consumerKey)

	// set the mapping from this validator's new consensus address on the consumer
	// to its consensus address on the provider;
	// note: this state must be deleted through the pruning mechanism
	k.SetValidatorByConsumerAddr(ctx, consumerId, consumerAddr, providerAddr)

	return nil
}

// GetProviderAddrFromConsumerAddr returns the consensus address of a validator with
// consAddr set as the consensus address on a consumer chain
func (k Keeper) GetProviderAddrFromConsumerAddr(
	ctx sdk.Context,
	consumerId string,
	consumerAddr types.ConsumerConsAddress,
) types.ProviderConsAddress {
	// check if this address is known only to the consumer chain
	if providerConsAddr, found := k.GetValidatorByConsumerAddr(ctx, consumerId, consumerAddr); found {
		return providerConsAddr
	}
	// If mapping from consumer -> provider addr is not found, there is no assigned key,
	// and the consumer addr is the provider addr
	return types.NewProviderConsAddress(consumerAddr.ToSdkConsAddr())
}

// PruneKeyAssignments prunes the consumer addresses no longer needed
// as they cannot be referenced in slash requests (by a correct consumer)
func (k Keeper) PruneKeyAssignments(ctx sdk.Context, consumerId string) {
	now := ctx.BlockTime()

	consumerAddrs := k.ConsumeConsumerAddrsToPrune(ctx, consumerId, now)
	for _, addrBz := range consumerAddrs.Addresses {
		consumerAddr := types.NewConsumerConsAddress(addrBz)
		k.DeleteValidatorByConsumerAddr(ctx, consumerId, consumerAddr)
		k.Logger(ctx).Info("consumer address was pruned",
			"consumer consumerId", consumerId,
			"consumer consensus addr", consumerAddr.String(),
		)
	}
}

// DeleteKeyAssignments deletes all the state needed for key assignments on a consumer chain
func (k Keeper) DeleteKeyAssignments(ctx sdk.Context, consumerId string) {
	// delete ValidatorConsumerPubKey
	for _, validatorConsumerAddr := range k.GetAllValidatorConsumerPubKeys(ctx, &consumerId) {
		providerAddr := types.NewProviderConsAddress(validatorConsumerAddr.ProviderAddr)
		k.DeleteValidatorConsumerPubKey(ctx, consumerId, providerAddr)
	}

	// delete ValidatorsByConsumerAddr
	for _, validatorConsumerAddr := range k.GetAllValidatorsByConsumerAddr(ctx, &consumerId) {
		consumerAddr := types.NewConsumerConsAddress(validatorConsumerAddr.ConsumerAddr)
		k.DeleteValidatorByConsumerAddr(ctx, consumerId, consumerAddr)
	}

	// delete ValidatorConsumerPubKey
	for _, consumerAddrsToPrune := range k.GetAllConsumerAddrsToPrune(ctx, consumerId) {
		k.DeleteConsumerAddrsToPrune(ctx, consumerId, consumerAddrsToPrune.PruneTs)
	}
}

// ValidatorConsensusKeyInUse checks if the given consensus key is already
// used by validator in a consumer chain.
// Note that this method is called when a new validator is created in the x/staking module of cosmos-sdk.
// In case it panics, the TX aborts and thus, the validator is not created. See AfterValidatorCreated hook.
func (k Keeper) ValidatorConsensusKeyInUse(ctx sdk.Context, valAddr sdk.ValAddress) bool {
	// Get the validator being added in the staking module.
	val, err := k.stakingKeeper.GetValidator(ctx, valAddr)
	if err != nil {
		// Abort TX, do NOT allow validator to be created
		panic(fmt.Errorf("error finding newly created validator in staking module: %w", err))
	}

	// Get the consensus address of the validator being added
	consensusAddr, err := val.GetConsAddr()
	if err != nil {
		// Abort TX, do NOT allow validator to be created
		panic("could not get validator cons addr ")
	}

	allConsumerIds := k.GetAllActiveConsumerIds(ctx)
	for _, c := range allConsumerIds {
		if _, exist := k.GetValidatorByConsumerAddr(ctx,
			c,
			types.NewConsumerConsAddress(consensusAddr),
		); exist {
			return true
		}
	}
	return false
}
