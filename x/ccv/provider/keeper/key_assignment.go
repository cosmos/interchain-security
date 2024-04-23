package keeper

import (
	"fmt"

	errorsmod "cosmossdk.io/errors"
	storetypes "cosmossdk.io/store/types"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	tmprotocrypto "github.com/cometbft/cometbft/proto/tendermint/crypto"

	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v5/x/ccv/types"
)

// GetValidatorConsumerPubKey returns a validator's public key assigned for a consumer chain
func (k Keeper) GetValidatorConsumerPubKey(
	ctx sdk.Context,
	chainID string,
	providerAddr types.ProviderConsAddress,
) (consumerKey tmprotocrypto.PublicKey, found bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerValidatorsKey(chainID, providerAddr))
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
	chainID string,
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
	store.Set(types.ConsumerValidatorsKey(chainID, providerAddr), bz)
}

// GetAllValidatorConsumerPubKeys gets all the validators public keys assigned for a consumer chain
// If chainID is nil, it returns all the validators public keys assigned for all consumer chains
//
// Note that the validators public keys assigned for a consumer chain are stored under keys
// with the following format: UnbondingOpIndexBytePrefix | len(chainID) | chainID | providerAddress
// Thus, the returned array is
//   - in ascending order of providerAddresses, if chainID is not nil;
//   - in undetermined order, if chainID is nil.
func (k Keeper) GetAllValidatorConsumerPubKeys(ctx sdk.Context, chainID *string) (validatorConsumerPubKeys []types.ValidatorConsumerPubKey) {
	store := ctx.KVStore(k.storeKey)
	var prefix []byte
	if chainID == nil {
		// iterate over the validators public keys assigned for all consumer chains
		prefix = []byte{types.ConsumerValidatorsBytePrefix}
	} else {
		// iterate over the validators public keys assigned for chainID
		prefix = types.ChainIdWithLenKey(types.ConsumerValidatorsBytePrefix, *chainID)
	}
	iterator := storetypes.KVStorePrefixIterator(store, prefix)
	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		// TODO: store chainID and provider cons address in value bytes, marshaled as protobuf type
		chainID, providerAddrTmp, err := types.ParseChainIdAndConsAddrKey(types.ConsumerValidatorsBytePrefix, iterator.Key())
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
			ChainId:      chainID,
			ProviderAddr: providerAddr.ToSdkConsAddr(),
			ConsumerKey:  &consumerKey,
		})
	}

	return validatorConsumerPubKeys
}

// DeleteValidatorConsumerPubKey deletes a validator's public key assigned for a consumer chain
func (k Keeper) DeleteValidatorConsumerPubKey(ctx sdk.Context, chainID string, providerAddr types.ProviderConsAddress) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerValidatorsKey(chainID, providerAddr))
}

// GetValidatorByConsumerAddr returns a validator's consensus address on the provider
// given the validator's consensus address on a consumer
func (k Keeper) GetValidatorByConsumerAddr(
	ctx sdk.Context,
	chainID string,
	consumerAddr types.ConsumerConsAddress,
) (providerAddr types.ProviderConsAddress, found bool) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ValidatorsByConsumerAddrKey(chainID, consumerAddr))
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
	chainID string,
	consumerAddr types.ConsumerConsAddress,
	providerAddr types.ProviderConsAddress,
) {
	store := ctx.KVStore(k.storeKey)
	// Cons address is a type alias for a byte string, no marshaling needed
	bz := providerAddr.ToSdkConsAddr()
	store.Set(types.ValidatorsByConsumerAddrKey(chainID, consumerAddr), bz)
}

// GetValidatorsByConsumerAddrs gets all the mappings from consensus addresses
// on a given consumer chain to consensus addresses on the provider chain.
// If chainID is nil, it returns all the mappings from consensus addresses on all consumer chains.
//
// Note that the mappings for a consumer chain are stored under keys with the following format:
// ValidatorsByConsumerAddrBytePrefix | len(chainID) | chainID | consumerAddress
// Thus, the returned array is
//   - in ascending order of consumerAddresses, if chainID is not nil;
//   - in undetermined order, if chainID is nil.
func (k Keeper) GetAllValidatorsByConsumerAddr(ctx sdk.Context, chainID *string) (validatorConsumerAddrs []types.ValidatorByConsumerAddr) {
	store := ctx.KVStore(k.storeKey)
	var prefix []byte
	if chainID == nil {
		// iterate over the mappings from consensus addresses on all consumer chains
		prefix = []byte{types.ValidatorsByConsumerAddrBytePrefix}
	} else {
		// iterate over the mappings from consensus addresses on chainID
		prefix = types.ChainIdWithLenKey(types.ValidatorsByConsumerAddrBytePrefix, *chainID)
	}
	iterator := storetypes.KVStorePrefixIterator(store, prefix)
	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		// TODO: store chainID and consumer cons address in value bytes, marshaled as protobuf type
		chainID, consumerAddrTmp, err := types.ParseChainIdAndConsAddrKey(types.ValidatorsByConsumerAddrBytePrefix, iterator.Key())
		if err != nil {
			// An error here would indicate something is very wrong,
			// store keys are assumed to be correctly serialized in SetValidatorByConsumerAddr.
			panic(fmt.Sprintf("failed to parse chainID and consumer address: %v", err))
		}
		consumerAddr := types.NewConsumerConsAddress(consumerAddrTmp)
		providerAddr := types.NewProviderConsAddress(iterator.Value())

		validatorConsumerAddrs = append(validatorConsumerAddrs, types.ValidatorByConsumerAddr{
			ConsumerAddr: consumerAddr.ToSdkConsAddr(),
			ProviderAddr: providerAddr.ToSdkConsAddr(),
			ChainId:      chainID,
		})
	}

	return validatorConsumerAddrs
}

// DeleteValidatorByConsumerAddr deletes the mapping from a validator's consensus address on a consumer
// to the validator's consensus address on the provider
func (k Keeper) DeleteValidatorByConsumerAddr(ctx sdk.Context, chainID string, consumerAddr types.ConsumerConsAddress) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ValidatorsByConsumerAddrKey(chainID, consumerAddr))
}

// AppendConsumerAddrsToPrune appends a consumer validator address to the list of consumer addresses
// that can be pruned once the VSCMaturedPacket with vscID is received.
//
// The following invariant needs to hold:
// For each consumer address cAddr in ValidatorByConsumerAddr,
//   - either there exists a provider address pAddr in ValidatorConsumerPubKey,
//     s.t. hash(ValidatorConsumerPubKey(pAddr)) = cAddr
//   - or there exists a vscID in ConsumerAddrsToPrune s.t. cAddr in ConsumerAddrsToPrune(vscID)
func (k Keeper) AppendConsumerAddrsToPrune(ctx sdk.Context, chainID string, vscID uint64, consumerAddr types.ConsumerConsAddress) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerAddrsToPruneKey(chainID, vscID))
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
	store.Set(types.ConsumerAddrsToPruneKey(chainID, vscID), bz)
}

// GetConsumerAddrsToPrune returns the list of consumer addresses
// that can be pruned once the VSCMaturedPacket with vscID is received
func (k Keeper) GetConsumerAddrsToPrune(
	ctx sdk.Context,
	chainID string,
	vscID uint64,
) (consumerAddrsToPrune types.AddressList) {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.ConsumerAddrsToPruneKey(chainID, vscID))
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

// GetAllConsumerAddrsToPrune gets all consumer addresses that can be pruned for a given chainID.
//
// Note that the list of all consumer addresses is stored under keys with the following format:
// ConsumerAddrsToPruneBytePrefix | len(chainID) | chainID | vscID
// Thus, the returned array is in ascending order of vscIDs.
func (k Keeper) GetAllConsumerAddrsToPrune(ctx sdk.Context, chainID string) (consumerAddrsToPrune []types.ConsumerAddrsToPrune) {
	store := ctx.KVStore(k.storeKey)
	iteratorPrefix := types.ChainIdWithLenKey(types.ConsumerAddrsToPruneBytePrefix, chainID)
	iterator := storetypes.KVStorePrefixIterator(store, iteratorPrefix)
	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		_, vscID, err := types.ParseChainIdAndUintIdKey(types.ConsumerAddrsToPruneBytePrefix, iterator.Key())
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

		consumerAddrsToPrune = append(consumerAddrsToPrune, types.ConsumerAddrsToPrune{
			VscId:         vscID,
			ConsumerAddrs: &addrs,
			ChainId:       chainID,
		})
	}

	return consumerAddrsToPrune
}

// DeleteConsumerAddrsToPrune deletes the list of consumer addresses mapped to a given VSC ID
func (k Keeper) DeleteConsumerAddrsToPrune(ctx sdk.Context, chainID string, vscID uint64) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.ConsumerAddrsToPruneKey(chainID, vscID))
}

// AssignConsumerKey assigns the consumerKey to the validator with providerAddr
// on the consumer chain with ID chainID, if it is either registered or currently
// voted on in a ConsumerAddition governance proposal
func (k Keeper) AssignConsumerKey(
	ctx sdk.Context,
	chainID string,
	validator stakingtypes.Validator,
	consumerKey tmprotocrypto.PublicKey,
) error {
	// check that the consumer chain is either registered or that
	// a ConsumerAdditionProposal was submitted.
	if !k.IsConsumerProposedOrRegistered(ctx, chainID) {
		return errorsmod.Wrapf(
			types.ErrUnknownConsumerChainId, chainID,
		)
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
		_, found := k.GetValidatorConsumerPubKey(ctx, chainID, providerAddr)
		if !found {
			return errorsmod.Wrapf(
				types.ErrCannotAssignDefaultKeyAssignment,
				"a validator cannot assign the default key assignment unless its key on that consumer has already been assigned",
			)
		}
	}

	if _, found := k.GetValidatorByConsumerAddr(ctx, chainID, consumerAddr); found {
		// consumer key is already in use
		// prevent multiple validators from assigning the same key
		return errorsmod.Wrapf(
			types.ErrConsumerKeyInUse, "a validator has assigned the consumer key already",
		)
	}

	// get the previous key assigned for this validator on this consumer chain
	if oldConsumerKey, found := k.GetValidatorConsumerPubKey(ctx, chainID, providerAddr); found {
		oldConsumerAddrTmp, err := ccvtypes.TMCryptoPublicKeyToConsAddr(oldConsumerKey)
		if err != nil {
			return err
		}
		oldConsumerAddr := types.NewConsumerConsAddress(oldConsumerAddrTmp)

		// check whether the consumer chain is already registered,
		// i.e., a client to the consumer was already created
		if _, consumerRegistered := k.GetConsumerClientId(ctx, chainID); consumerRegistered {
			// mark the old consumer address as prunable once the VSCMaturedPacket
			// for the current VSC ID is received;
			// note: this state is removed on receiving the VSCMaturedPacket
			k.AppendConsumerAddrsToPrune(
				ctx,
				chainID,
				k.GetValidatorSetUpdateId(ctx),
				oldConsumerAddr,
			)
		} else {
			// if the consumer chain is not registered, then remove the mapping
			// from the old consumer address to the provider address
			k.DeleteValidatorByConsumerAddr(ctx, chainID, oldConsumerAddr)
		}
	}

	// set the mapping from this validator's provider address to the new consumer key;
	// overwrite if already exists
	// note: this state is deleted when the validator is removed from the staking module
	k.SetValidatorConsumerPubKey(ctx, chainID, providerAddr, consumerKey)

	// set the mapping from this validator's new consensus address on the consumer
	// to its consensus address on the provider;
	// note: this state must be deleted through the pruning mechanism
	k.SetValidatorByConsumerAddr(ctx, chainID, consumerAddr, providerAddr)

	return nil
}

// GetProviderAddrFromConsumerAddr returns the consensus address of a validator with
// consAddr set as the consensus address on a consumer chain
func (k Keeper) GetProviderAddrFromConsumerAddr(
	ctx sdk.Context,
	chainID string,
	consumerAddr types.ConsumerConsAddress,
) types.ProviderConsAddress {
	// check if this address is known only to the consumer chain
	if providerConsAddr, found := k.GetValidatorByConsumerAddr(ctx, chainID, consumerAddr); found {
		return providerConsAddr
	}
	// If mapping from consumer -> provider addr is not found, there is no assigned key,
	// and the consumer addr is the provider addr
	return types.NewProviderConsAddress(consumerAddr.ToSdkConsAddr())
}

// PruneKeyAssignments prunes the consumer addresses no longer needed
// as they cannot be referenced in slash requests (by a correct consumer)
func (k Keeper) PruneKeyAssignments(ctx sdk.Context, chainID string, vscID uint64) {
	consumerAddrs := k.GetConsumerAddrsToPrune(ctx, chainID, vscID)
	for _, addrBz := range consumerAddrs.Addresses {
		consumerAddr := types.NewConsumerConsAddress(addrBz)
		k.DeleteValidatorByConsumerAddr(ctx, chainID, consumerAddr)
		k.Logger(ctx).Info("consumer address was pruned",
			"consumer chainID", chainID,
			"consumer consensus addr", consumerAddr.String(),
		)
	}

	k.DeleteConsumerAddrsToPrune(ctx, chainID, vscID)
}

// DeleteKeyAssignments deletes all the state needed for key assignments on a consumer chain
func (k Keeper) DeleteKeyAssignments(ctx sdk.Context, chainID string) {
	// delete ValidatorConsumerPubKey
	for _, validatorConsumerAddr := range k.GetAllValidatorConsumerPubKeys(ctx, &chainID) {
		providerAddr := types.NewProviderConsAddress(validatorConsumerAddr.ProviderAddr)
		k.DeleteValidatorConsumerPubKey(ctx, chainID, providerAddr)
	}

	// delete ValidatorsByConsumerAddr
	for _, validatorConsumerAddr := range k.GetAllValidatorsByConsumerAddr(ctx, &chainID) {
		consumerAddr := types.NewConsumerConsAddress(validatorConsumerAddr.ConsumerAddr)
		k.DeleteValidatorByConsumerAddr(ctx, chainID, consumerAddr)
	}

	// delete ValidatorConsumerPubKey
	for _, consumerAddrsToPrune := range k.GetAllConsumerAddrsToPrune(ctx, chainID) {
		k.DeleteConsumerAddrsToPrune(ctx, chainID, consumerAddrsToPrune.VscId)
	}
}

// IsConsumerProposedOrRegistered checks if a consumer chain is either registered, meaning either already running
// or will run soon, or proposed its ConsumerAdditionProposal was submitted but the chain was not yet added to ICS yet.
func (k Keeper) IsConsumerProposedOrRegistered(ctx sdk.Context, chainID string) bool {
	allConsumerChains := k.GetAllRegisteredAndProposedChainIDs(ctx)
	for _, c := range allConsumerChains {
		if c == chainID {
			return true
		}
	}

	return false
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
		panic(fmt.Errorf("error finding newly created validator in staking module: %s", err))
	}

	// Get the consensus address of the validator being added
	consensusAddr, err := val.GetConsAddr()
	if err != nil {
		// Abort TX, do NOT allow validator to be created
		panic("could not get validator cons addr ")
	}

	allConsumerChains := k.GetAllRegisteredAndProposedChainIDs(ctx)
	for _, c := range allConsumerChains {
		if _, exist := k.GetValidatorByConsumerAddr(ctx,
			c,
			types.NewConsumerConsAddress(consensusAddr),
		); exist {
			return true
		}
	}
	return false
}
