package keeper

import (
	"errors"
	"sort"

	sdk "github.com/cosmos/cosmos-sdk/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"

	abci "github.com/tendermint/tendermint/abci/types"

	utils "github.com/cosmos/interchain-security/x/ccv/utils"
	tmprotocrypto "github.com/tendermint/tendermint/proto/tendermint/crypto"
)

type VSCID = uint64
type ProviderKey = tmprotocrypto.PublicKey
type ConsumerKey = tmprotocrypto.PublicKey
type ProviderAddr = sdk.ConsAddress
type ConsumerAddr = sdk.ConsAddress

type Store interface {
	SetProviderConsAddrToConsumerPublicKey(ProviderAddr, ConsumerKey)
	GetProviderConsAddrToConsumerPublicKey(ProviderAddr) (ConsumerKey, bool)
	DelProviderConsAddrToConsumerPublicKey(ProviderAddr)
	IterateProviderConsAddrToConsumerPublicKey(func(ProviderAddr, ConsumerKey) bool)

	SetConsumerPublicKeyToProviderPublicKey(ConsumerKey, ProviderKey)
	GetConsumerPublicKeyToProviderPublicKey(ConsumerKey) (ProviderKey, bool)
	DelConsumerPublicKeyToProviderPublicKey(ConsumerKey)
	IterateConsumerPublicKeyToProviderPublicKey(func(ConsumerKey, ProviderKey) bool)

	SetConsumerConsAddrToLastUpdateMemo(ConsumerAddr, providertypes.LastUpdateMemo)
	GetConsumerConsAddrToLastUpdateMemo(ConsumerAddr) (providertypes.LastUpdateMemo, bool)
	DelConsumerConsAddrToLastUpdateMemo(ConsumerAddr)
	IterateConsumerConsAddrToLastUpdateMemo(func(ConsumerAddr, providertypes.LastUpdateMemo) bool)
}

// KeyAssignment is a wrapper around a storage API which implements the key assignment features
// allowing a provider to assign a consumer key to a provider key and vice versa.
// Please see docs/key-assignment/design.md for more details.
type KeyAssignment struct {
	Store Store
}

func MakeKeyAssignment(store Store) KeyAssignment {
	return KeyAssignment{
		Store: store,
	}
}

// SetProviderPubKeyToConsumerPubKey tries to assign a mapping from the provider key to the consumer key.
// The operation can fail if the consumer key is or was recently assigned to by a provider key. This is a
// security feature.
func (ka *KeyAssignment) SetProviderPubKeyToConsumerPubKey(pk ProviderKey, ck ConsumerKey) error {
	if _, ok := ka.Store.GetConsumerPublicKeyToProviderPublicKey(ck); ok {
		return errors.New(`cannot reuse key which is in use or was recently in use`)
	}
	if _, ok := ka.Store.GetConsumerConsAddrToLastUpdateMemo(utils.TMCryptoPublicKeyToConsAddr(ck)); ok {
		return errors.New(`cannot reuse key which is in use or was recently in use`)
	}
	pca := utils.TMCryptoPublicKeyToConsAddr(pk)
	if oldCk, ok := ka.Store.GetProviderConsAddrToConsumerPublicKey(pca); ok {
		ka.Store.DelConsumerPublicKeyToProviderPublicKey(oldCk)
	}
	ka.Store.SetProviderConsAddrToConsumerPublicKey(pca, ck)
	ka.Store.SetConsumerPublicKeyToProviderPublicKey(ck, pk)
	return nil
}

// DeleteProviderKey removes all KeyAssignment data associated to the provider validator
// with key pca. This is called when a validator is destroyed in the staking module.
// This is relatively expensive, but should be called rarely because validators are
// destroyed rarely.
func (ka *KeyAssignment) DeleteProviderKey(pca ProviderAddr) {
	// Delete the current mapping from the consumer key to the provider key
	if ck, ok := ka.Store.GetProviderConsAddrToConsumerPublicKey(pca); ok {
		// Delete the current mapping from the provider key to the consumer key
		ka.Store.DelProviderConsAddrToConsumerPublicKey(pca)
		// and the current mapping from the consumer key to the provider key
		ka.Store.DelConsumerPublicKeyToProviderPublicKey(ck)
	}
	toDelete := []ConsumerAddr{}
	// Find all the consumer keys which were mapped to by the provider key
	// in order to delete them
	ka.Store.IterateConsumerConsAddrToLastUpdateMemo(func(cca ConsumerAddr, lum providertypes.LastUpdateMemo) bool {
		pcaInMemo := utils.TMCryptoPublicKeyToConsAddr(*lum.ProviderKey)
		if pca.Equals(pcaInMemo) {
			toDelete = append(toDelete, cca)
		}
		return false
	})
	// Delete the mappings from the consumer keys to the provider keys
	for _, cca := range toDelete {
		ka.Store.DelConsumerConsAddrToLastUpdateMemo(cca)
	}
}

// GetCurrentConsumerPubKeyFromProviderPubKey returns the current consumer key assigned to the provider key.
func (ka *KeyAssignment) GetCurrentConsumerPubKeyFromProviderPubKey(pk ProviderKey) (ck ConsumerKey, found bool) {
	return ka.Store.GetProviderConsAddrToConsumerPublicKey(utils.TMCryptoPublicKeyToConsAddr(pk))
}

// GetProviderPubKeyFromConsumerPubKey returns any provider key which is currently assigned to the consumer key.
func (ka *KeyAssignment) GetProviderPubKeyFromConsumerPubKey(ck ConsumerKey) (pk ProviderKey, found bool) {
	return ka.Store.GetConsumerPublicKeyToProviderPublicKey(ck)
}

// GetProviderPubKeyFromConsumerConsAddress returns the provider key which was associated to the consumer key with
// consensus address cca at the last update that used the consumer key.
func (ka *KeyAssignment) GetProviderPubKeyFromConsumerConsAddress(cca sdk.ConsAddress) (pk ProviderKey, found bool) {
	if lum, found := ka.Store.GetConsumerConsAddrToLastUpdateMemo(cca); found {
		return *lum.ProviderKey, true
	}
	return pk, false
}

// PruneUnusedKeys deletes from the store all of the consumer keys which the consumer chain has matured, based
// on latestMatureVscid, and for which it sure that the correct consumer chain can no longer reference the key
// in a downtime or double sign slash instruction.
func (ka *KeyAssignment) PruneUnusedKeys(latestMatureVscid VSCID) {
	toDel := []ConsumerAddr{}
	ka.Store.IterateConsumerConsAddrToLastUpdateMemo(func(cca ConsumerAddr, lum providertypes.LastUpdateMemo) bool {
		if lum.Power == 0 && lum.Vscid <= latestMatureVscid {
			toDel = append(toDel, cca)
		}
		return false
	})
	for _, cca := range toDel {
		ka.Store.DelConsumerConsAddrToLastUpdateMemo(cca)
	}
}

// DeterministicStringify returns a deterministic string representation of the
// key. This is useful to identify like keys with different representations.
func DeterministicStringify(k tmprotocrypto.PublicKey) string {
	bz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	return string(bz)
}

// KeyToPower is an implementation of a map from a public key to a power.
// It is used because public keys are not comparable in Go, so they cannot be
// used as builtin map keys.
type KeyToPower struct {
	inner     map[tmprotocrypto.PublicKey]int64
	canonical map[string]tmprotocrypto.PublicKey
}

func MakeKeyToPower() KeyToPower {
	return KeyToPower{
		inner:     map[tmprotocrypto.PublicKey]int64{},
		canonical: map[string]tmprotocrypto.PublicKey{},
	}
}

// Set is a typical map set operation.
func (m *KeyToPower) Set(pk tmprotocrypto.PublicKey, power int64) {
	stringified := DeterministicStringify(pk)
	if k, found := m.canonical[stringified]; found {
		pk = k
	} else {
		m.canonical[stringified] = pk
	}
	m.inner[pk] = power
}

// Get is a typical map get operation.
func (m *KeyToPower) Get(pk tmprotocrypto.PublicKey) (int64, bool) {
	if k, found := m.canonical[DeterministicStringify(pk)]; found {
		power, found := m.inner[k]
		if !found {
			panic("found canonical key but key not present in inner map")
		}
		return power, true
	}
	return -1, false
}

// KeyToLastUpdateMemo is an implementation of a map from a public key to a
// memo storing the last update.
// It is used because public keys are not comparable in Go, so they cannot be
// used as builtin map keys.
type KeyToLastUpdateMemo struct {
	inner     map[tmprotocrypto.PublicKey]providertypes.LastUpdateMemo
	canonical map[string]tmprotocrypto.PublicKey
}

func MakeKeyToLastUpdateMemo() KeyToLastUpdateMemo {
	return KeyToLastUpdateMemo{
		inner:     map[tmprotocrypto.PublicKey]providertypes.LastUpdateMemo{},
		canonical: map[string]tmprotocrypto.PublicKey{},
	}
}

// Set is a typical map set operation.
func (m *KeyToLastUpdateMemo) Set(pk tmprotocrypto.PublicKey, memo providertypes.LastUpdateMemo) {
	stringified := DeterministicStringify(pk)
	if k, found := m.canonical[stringified]; found {
		pk = k
	} else {
		m.canonical[stringified] = pk
	}
	m.inner[pk] = memo
}

// Get is a typical map get operation.
func (m *KeyToLastUpdateMemo) Get(pk tmprotocrypto.PublicKey) (providertypes.LastUpdateMemo, bool) {
	if k, found := m.canonical[DeterministicStringify(pk)]; found {
		memo, found := m.inner[k]
		if !found {
			panic("found canonical key but key not present in inner map")
		}
		return memo, true
	}
	return providertypes.LastUpdateMemo{}, false
}

// KeySet is an implementation of a set of public keys.
// It is used because public keys are not comparable in Go
// so they cannot be used as builtin map keys.
type KeySet struct {
	inner     map[tmprotocrypto.PublicKey]struct{}
	canonical map[string]tmprotocrypto.PublicKey
}

func MakeKeySet() KeySet {
	return KeySet{
		inner:     map[tmprotocrypto.PublicKey]struct{}{},
		canonical: map[string]tmprotocrypto.PublicKey{},
	}
}

// Add is a typical set add operation.
func (s *KeySet) Add(pk tmprotocrypto.PublicKey) {
	stringified := DeterministicStringify(pk)
	if k, found := s.canonical[stringified]; found {
		pk = k
	} else {
		s.canonical[stringified] = pk
	}
	s.inner[pk] = struct{}{}
}

// Add is a typical set has/contains operation.
func (s *KeySet) Has(pk tmprotocrypto.PublicKey) bool {
	_, found := s.canonical[DeterministicStringify(pk)]
	return found
}

// getProviderKeysForUpdate returns the all the provider keys of validators for which
// an update must be sent. An update must be sent to the consumer if, either:
//  1. The consumer has the validator in its active set AND the assigned key for the
//     validator has changed since the last update.
//  2. The voting power of the validator has changed, and the validator is in the active
//     set.
func (ka *KeyAssignment) getProviderKeysForUpdate(stakingUpdates KeyToPower) KeySet {

	ret := MakeKeySet()

	// Get provider keys which the consumer is aware of, because the
	// last update sent to the consumer was a positive power update
	// and the assigned key has changed since that update.
	ka.Store.IterateConsumerConsAddrToLastUpdateMemo(func(cca ConsumerAddr, lum providertypes.LastUpdateMemo) bool {
		pca := utils.TMCryptoPublicKeyToConsAddr(*lum.ProviderKey)
		if newCk, ok := ka.Store.GetProviderConsAddrToConsumerPublicKey(pca); ok {
			oldCk := lum.ConsumerKey
			// Key changed? Last power was positive?
			if !oldCk.Equal(newCk) && 0 < lum.Power {
				ret.Add(*lum.ProviderKey)
			}
		}
		return false
	})

	// Get provider keys where the validator power has changed
	for providerPublicKey := range stakingUpdates.inner {
		ret.Add(providerPublicKey)
	}

	return ret
}

// getProviderKeysLastPositiveUpdate returns a map of provider keys to a memo of the last update
// associated to the key, if that update was positive, and that update is included in mustCreateUpdate.
func (ka KeyAssignment) getProviderKeysLastPositiveUpdate(mustCreateUpdate KeySet) KeyToLastUpdateMemo {
	lastUpdate := MakeKeyToLastUpdateMemo()
	ka.Store.IterateConsumerConsAddrToLastUpdateMemo(func(_ ConsumerAddr, lum providertypes.LastUpdateMemo) bool {
		if 0 < lum.Power {
			if mustCreateUpdate.Has(*lum.ProviderKey) {
				lastUpdate.Set(*lum.ProviderKey, lum)
			}
		}
		return false
	})
	return lastUpdate
}

// do inner work as part of ComputeUpdates
func (ka *KeyAssignment) getConsumerUpdates(vscid VSCID, stakingUpdates KeyToPower) KeyToPower {

	// Init the return data structure
	consumerUpdates := MakeKeyToPower()

	// Get a set of all the provider validator keys for which an update must be sent
	providerKeysForUpdate := ka.getProviderKeysForUpdate(stakingUpdates)

	// Get the LAST positive update for each provider validator key that needs an update
	providerKeysLastPositivePowerUpdateMemo := ka.getProviderKeysLastPositiveUpdate(providerKeysForUpdate)

	/*
		Create a deletion (zero power) update for any consumer key known to the consumer
		that is no longer in use, or for which the power has changed to zero or a positive
		number.

		The purpose of *this* step is to create a clean slate. The *next* step will
		amend the updates for any validators with a positive power.
	*/
	for loopPk := range providerKeysForUpdate.inner {
		// For each provider key for which there was already a positive update
		// create a deletion update for the associated consumer key.
		pk := loopPk // Avoid taking the address of the loop variable
		if lum, found := providerKeysLastPositivePowerUpdateMemo.Get(pk); found {
			cca := utils.TMCryptoPublicKeyToConsAddr(*lum.ConsumerKey)
			ka.Store.SetConsumerConsAddrToLastUpdateMemo(cca, providertypes.LastUpdateMemo{ConsumerKey: lum.ConsumerKey, ProviderKey: &pk, Vscid: vscid, Power: 0})
			consumerUpdates.Set(*lum.ConsumerKey, 0)
		}
	}

	/*
		Create a positive power update for any consumer key which is in use.

		The purpose of this step is to ensure that the consumer is sent the latest
		positive power update for any validator for which the power is positive.
	*/
	for loopPk := range providerKeysForUpdate.inner {
		pk := loopPk // Avoid taking the address of the loop variable

		// For each provider key where there was either
		// 1) already a positive power update
		// 2) the validator power has changed (and is positive)
		// create a change update for the associated consumer key.

		var power int64 = 0

		if lum, found := providerKeysLastPositivePowerUpdateMemo.Get(pk); found {
			// There was previously a positive power update: copy it.
			power = lum.Power
		}

		// There is a new validator power: use it. It takes precedence.
		if updatedVotingPower, ok := stakingUpdates.Get(pk); ok {
			power = updatedVotingPower
		}

		// Only ship update with positive powers.
		if 0 < power {
			ck, found := ka.Store.GetProviderConsAddrToConsumerPublicKey(utils.TMCryptoPublicKeyToConsAddr(pk))
			if !found {
				panic("must find ck for pk")
			}
			cca := utils.TMCryptoPublicKeyToConsAddr(ck)
			ka.Store.SetConsumerConsAddrToLastUpdateMemo(cca, providertypes.LastUpdateMemo{ConsumerKey: &ck, ProviderKey: &pk, Vscid: vscid, Power: power})
			consumerUpdates.Set(ck, power)
		}
	}

	return consumerUpdates
}

// ComputeUpdates takes a validator power updates as produced by the staking module and returns a set of updates
// which can be sent to the consumer. This is a stateful operation. The updates produced ensure that the consumer
// updates represent a consistent validator set in the presence of validator set changes and validator key
// assignment changes.
// The vscid is used in the pruning mechanism. Positive power updates produced by a call to this function with a
// given vscid will not be prunable until the vscid matures.
func (ka *KeyAssignment) ComputeUpdates(vscid VSCID, stakingUpdates []abci.ValidatorUpdate) []abci.ValidatorUpdate {

	// Create a map of provider keys to power
	keyToPower := MakeKeyToPower()
	for _, u := range stakingUpdates {
		keyToPower.Set(u.PubKey, u.Power)
	}

	// Get the consumerUpdates to send to the consumer
	consumerUpdates := ka.getConsumerUpdates(vscid, keyToPower)

	// Transform the consumer updates back into a list for sending to the consumer
	// The consumer will aggregate updates and ultimately send them to tendermint.
	tendermintUpdates := []abci.ValidatorUpdate{}
	for ck, power := range consumerUpdates.inner {
		tendermintUpdates = append(tendermintUpdates, abci.ValidatorUpdate{PubKey: ck, Power: power})
	}

	// Sort for determinism across nodes.
	sort.Slice(tendermintUpdates, func(i, j int) bool {
		if tendermintUpdates[i].Power > tendermintUpdates[j].Power {
			return true
		}
		return tendermintUpdates[i].PubKey.String() > tendermintUpdates[j].PubKey.String()
	})

	return tendermintUpdates
}

// AssignDefaultsForProviderKeysWithoutExplicitAssignments assigns the default consumer key to any provider key
// for which a consumer key has not been explicitly assigned.
func (ka *KeyAssignment) AssignDefaultsForProviderKeysWithoutExplicitAssignments(updates []abci.ValidatorUpdate) {
	for _, u := range updates {
		if _, found := ka.GetCurrentConsumerPubKeyFromProviderPubKey(u.PubKey); !found {
			// The provider has not designated a key to use for the consumer chain. Use the provider key
			// by default.
			_ = ka.SetProviderPubKeyToConsumerPubKey(u.PubKey, u.PubKey)
		}
	}
}

// AssignDefaultsAndComputeUpdates is a convenience function which calls AssignDefaultsForProviderKeysWithoutExplicitAssignments
// and also computes the latest set of updates to send to the consumer using ComputeUpdates.
func (ka *KeyAssignment) AssignDefaultsAndComputeUpdates(vscid VSCID, stakingUpdates []abci.ValidatorUpdate) (consumerUpdates []abci.ValidatorUpdate) {
	ka.AssignDefaultsForProviderKeysWithoutExplicitAssignments(stakingUpdates)
	return ka.ComputeUpdates(vscid, stakingUpdates)
}

// Returns true iff internal invariants hold. For testing. Expensive.
func (ka *KeyAssignment) InternalInvariants() bool {

	good := true

	{
		// No two provider keys can map to the same consumer key
		// (ProviderConsAddrToConsumerPublicKey is sane)
		seen := map[string]bool{}
		ka.Store.IterateProviderConsAddrToConsumerPublicKey(func(_ ProviderAddr, ck ConsumerKey) bool {
			if seen[DeterministicStringify(ck)] {
				good = false
			}
			seen[DeterministicStringify(ck)] = true
			return false
		})
	}

	{
		// All values of ProviderConsAddrToConsumerPublicKey is a key of ConsumerPublicKeyToProviderPublicKey
		// (reverse lookup is always possible)
		ka.Store.IterateProviderConsAddrToConsumerPublicKey(func(pca ProviderAddr, ck ConsumerKey) bool {
			if pkQueried, ok := ka.Store.GetConsumerPublicKeyToProviderPublicKey(ck); ok {
				pcaQueried := utils.TMCryptoPublicKeyToConsAddr(pkQueried)
				good = good && string(pcaQueried) == string(pca)
			} else {
				good = false
			}
			return false
		})
	}

	{
		// All consumer keys mapping to provider keys are actually
		// mapped to by the provider key.
		// (ckToPk is sane)
		ka.Store.IterateConsumerPublicKeyToProviderPublicKey(func(ck ConsumerKey, _ ProviderKey) bool {
			found := false
			ka.Store.IterateProviderConsAddrToConsumerPublicKey(func(_ ProviderAddr, candidateCk ConsumerKey) bool {
				if candidateCk.Equal(ck) {
					found = true
					return true
				}
				return false
			})
			good = good && found
			return false
		})
	}

	{
		// If a consumer key is mapped to a provider key (currently)
		// any last update memo containing the same consumer key has the same
		// mapping.
		// (Ensures lookups are correct)
		ka.Store.IterateConsumerPublicKeyToProviderPublicKey(func(ck ConsumerKey, pk ProviderKey) bool {
			if m, ok := ka.Store.GetConsumerConsAddrToLastUpdateMemo(utils.TMCryptoPublicKeyToConsAddr(ck)); ok {
				if !pk.Equal(m.ProviderKey) {
					good = false
				}
			}
			return false
		})
	}

	{
		// All entries in ConsumerConsAddrToLastUpdateMemo have a consumer consensus
		// address which is the address held inside
		ka.Store.IterateConsumerConsAddrToLastUpdateMemo(func(cca ConsumerAddr, lum providertypes.LastUpdateMemo) bool {
			consAddr := utils.TMCryptoPublicKeyToConsAddr(*lum.ConsumerKey)
			good = good && cca.Equals(consAddr)
			return false
		})
	}

	{
		// The set of all LastUpdateMemos with positive power
		// has pairwise unique provider keys
		seen := map[string]bool{}
		ka.Store.IterateConsumerConsAddrToLastUpdateMemo(func(_ ConsumerAddr, lum providertypes.LastUpdateMemo) bool {
			if 0 < lum.Power {
				s := DeterministicStringify(*lum.ProviderKey)
				if _, ok := seen[s]; ok {
					good = false
				}
				seen[s] = true

			}
			return false
		})
	}

	return good

}

type KeyAssignmentStore struct {
	Store   sdk.KVStore
	ChainID string
}

func (s *KeyAssignmentStore) SetProviderConsAddrToConsumerPublicKey(k ProviderAddr, v ConsumerKey) {
	kbz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	vbz, err := v.Marshal()
	if err != nil {
		panic(err)
	}
	s.Store.Set(providertypes.KeyAssignmentProviderConsAddrToConsumerPublicKeyKey(s.ChainID, kbz), vbz)
}

func (s *KeyAssignmentStore) SetConsumerPublicKeyToProviderPublicKey(k ConsumerKey, v ProviderKey) {
	kbz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	vbz, err := v.Marshal()
	if err != nil {
		panic(err)
	}
	s.Store.Set(providertypes.KeyAssignmentConsumerPublicKeyToProviderPublicKeyKey(s.ChainID, kbz), vbz)
}

func (s *KeyAssignmentStore) SetConsumerConsAddrToLastUpdateMemo(k ConsumerAddr, v providertypes.LastUpdateMemo) {
	kbz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	vbz, err := v.Marshal()
	if err != nil {
		panic(err)
	}
	s.Store.Set(providertypes.KeyAssignmentConsumerConsAddrToLastUpdateMemoKey(s.ChainID, kbz), vbz)
}

func (s *KeyAssignmentStore) GetProviderConsAddrToConsumerPublicKey(k ProviderAddr) (v ConsumerKey, found bool) {
	kbz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	if vbz := s.Store.Get(providertypes.KeyAssignmentProviderConsAddrToConsumerPublicKeyKey(s.ChainID, kbz)); vbz != nil {
		err := v.Unmarshal(vbz)
		if err != nil {
			panic(err)
		}
		return v, true
	}
	return v, false
}

func (s *KeyAssignmentStore) GetConsumerPublicKeyToProviderPublicKey(k ConsumerKey) (v ProviderKey, found bool) {
	kbz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	if vbz := s.Store.Get(providertypes.KeyAssignmentConsumerPublicKeyToProviderPublicKeyKey(s.ChainID, kbz)); vbz != nil {
		err := v.Unmarshal(vbz)
		if err != nil {
			panic(err)
		}
		return v, true
	}
	return v, false
}

func (s *KeyAssignmentStore) GetConsumerConsAddrToLastUpdateMemo(k ConsumerAddr) (v providertypes.LastUpdateMemo, found bool) {
	kbz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	if vbz := s.Store.Get(providertypes.KeyAssignmentConsumerConsAddrToLastUpdateMemoKey(s.ChainID, kbz)); vbz != nil {
		v := providertypes.LastUpdateMemo{}
		err := v.Unmarshal(vbz)
		if err != nil {
			panic(err)
		}
		return v, true
	}
	return v, false
}

func (s *KeyAssignmentStore) DelProviderConsAddrToConsumerPublicKey(k ProviderAddr) {
	kbz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	s.Store.Delete(providertypes.KeyAssignmentProviderConsAddrToConsumerPublicKeyKey(s.ChainID, kbz))
}

func (s *KeyAssignmentStore) DelConsumerPublicKeyToProviderPublicKey(k ConsumerKey) {
	kbz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	s.Store.Delete(providertypes.KeyAssignmentConsumerPublicKeyToProviderPublicKeyKey(s.ChainID, kbz))
}

func (s *KeyAssignmentStore) DelConsumerConsAddrToLastUpdateMemo(k ConsumerAddr) {
	kbz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	s.Store.Delete(providertypes.KeyAssignmentConsumerConsAddrToLastUpdateMemoKey(s.ChainID, kbz))
}

func (s *KeyAssignmentStore) IterateProviderConsAddrToConsumerPublicKey(stop func(ProviderAddr, ConsumerKey) (stop bool)) {
	prefix := providertypes.KeyAssignmentProviderConsAddrToConsumerPublicKeyChainPrefix(s.ChainID)
	iterator := sdk.KVStorePrefixIterator(s.Store, prefix)
	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		k := ProviderAddr{}
		err := k.Unmarshal(iterator.Key()[len(prefix):])
		if err != nil {
			panic(err)
		}
		v := ConsumerKey{}
		err = v.Unmarshal(iterator.Value())
		if err != nil {
			panic(err)
		}
		if stop(k, v) {
			return
		}
	}
}

func (s *KeyAssignmentStore) IterateConsumerPublicKeyToProviderPublicKey(stop func(ConsumerKey, ProviderKey) (stop bool)) {
	prefix := providertypes.KeyAssignmentConsumerPublicKeyToProviderPublicKeyChainPrefix(s.ChainID)
	iterator := sdk.KVStorePrefixIterator(s.Store, prefix)
	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		k := ConsumerKey{}
		err := k.Unmarshal(iterator.Key()[len(prefix):])
		if err != nil {
			panic(err)
		}
		v := ProviderKey{}
		err = v.Unmarshal(iterator.Value())
		if err != nil {
			panic(err)
		}
		if stop(k, v) {
			return
		}
	}
}

func (s *KeyAssignmentStore) IterateConsumerConsAddrToLastUpdateMemo(stop func(ConsumerAddr, providertypes.LastUpdateMemo) (stop bool)) {
	prefix := providertypes.KeyAssignmentConsumerConsAddrToLastUpdateMemoChainPrefix(s.ChainID)
	iterator := sdk.KVStorePrefixIterator(s.Store, prefix)
	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		k := ConsumerAddr{}
		err := k.Unmarshal(iterator.Key()[len(prefix):])
		if err != nil {
			panic(err)
		}
		v := providertypes.LastUpdateMemo{}
		err = v.Unmarshal(iterator.Value())
		if err != nil {
			panic(err)
		}
		if stop(k, v) {
			return
		}
	}
}

// Delete all of the key assignment data associated to the given chain ID.
func (k Keeper) DeleteKeyAssignment(ctx sdk.Context, chainID string) {
	store := ctx.KVStore(k.storeKey)
	for _, pref := range [][]byte{
		providertypes.KeyAssignmentProviderConsAddrToConsumerPublicKeyChainPrefix(chainID),
		providertypes.KeyAssignmentConsumerPublicKeyToProviderPublicKeyChainPrefix(chainID),
		providertypes.KeyAssignmentConsumerConsAddrToLastUpdateMemoChainPrefix(chainID),
	} {
		iter := sdk.KVStorePrefixIterator(store, pref)
		defer iter.Close()
		for ; iter.Valid(); iter.Next() {
			store.Delete(iter.Key())
		}
	}
}

// GetProviderConsAddrForSlashing returns the cons address of the validator to be slashed
// on the provider chain. It looks up the provider's consensus address from past key assignments.
func (k Keeper) GetProviderConsAddrForSlashing(ctx sdk.Context, chainID string, consumerAddress []byte) (sdk.ConsAddress, error) {
	consumerConsAddr := sdk.ConsAddress(consumerAddress)
	providerPublicKey, found := k.KeyAssignment(ctx, chainID).GetProviderPubKeyFromConsumerConsAddress(consumerConsAddr)
	if !found {
		// It is possible for a faulty consumer chain to send a slash packet for a validator that does
		// not have a key assignment on the provider chain. In this case, we do not slash the validator
		// and do not panic.
		return nil, errors.New("could not find provider address for slashing")
	}
	return utils.TMCryptoPublicKeyToConsAddr(providerPublicKey), nil
}

func (k Keeper) KeyAssignment(ctx sdk.Context, chainID string) *KeyAssignment {
	store := KeyAssignmentStore{ctx.KVStore(k.storeKey), chainID}
	ka := MakeKeyAssignment(&store)
	return &ka
}
