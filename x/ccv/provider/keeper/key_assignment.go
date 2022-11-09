package keeper

import (
	"errors"
	"sort"

	sdk "github.com/cosmos/cosmos-sdk/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"

	sdkcryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"

	abci "github.com/tendermint/tendermint/abci/types"

	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	tmprotocrypto "github.com/tendermint/tendermint/proto/tendermint/crypto"
)

// In this branch I am icing things for a few days.

type VSCID = uint64
type ProviderPublicKey = tmprotocrypto.PublicKey
type ConsumerPublicKey = tmprotocrypto.PublicKey
type ProviderConsAddr = sdk.ConsAddress
type ConsumerConsAddr = sdk.ConsAddress

func DeterministicStringify(k tmprotocrypto.PublicKey) string {
	bz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	return string(bz)
}

func TMCryptoPublicKeyToConsAddr(k tmprotocrypto.PublicKey) sdk.ConsAddress {
	sdkK, err := sdkcryptocodec.FromTmProtoPublicKey(k)
	if err != nil {
		panic("could not get public key from tm proto public key")
	}
	return sdk.GetConsAddress(sdkK)
}

type Store interface {
	SetProviderConsAddrToConsumerPublicKey(ProviderConsAddr, ConsumerPublicKey)
	GetProviderConsAddrToConsumerPublicKey(ProviderConsAddr) (ConsumerPublicKey, bool)
	DelProviderConsAddrToConsumerPublicKey(ProviderConsAddr)
	IterateProviderConsAddrToConsumerPublicKey(func(ProviderConsAddr, ConsumerPublicKey) bool)
	SetConsumerPublicKeyToProviderPublicKey(ConsumerPublicKey, ProviderPublicKey)
	GetConsumerPublicKeyToProviderPublicKey(ConsumerPublicKey) (ProviderPublicKey, bool)
	DelConsumerPublicKeyToProviderPublicKey(ConsumerPublicKey)
	IterateConsumerConsAddrToLastUpdateMemo(func(ConsumerConsAddr, providertypes.LastUpdateMemo) bool)
	SetConsumerConsAddrToLastUpdateMemo(ConsumerConsAddr, providertypes.LastUpdateMemo)
	GetConsumerConsAddrToLastUpdateMemo(ConsumerConsAddr) (providertypes.LastUpdateMemo, bool)
	DelConsumerConsAddrToLastUpdateMemo(ConsumerConsAddr)
	IterateConsumerPublicKeyToProviderPublicKey(func(ConsumerPublicKey, ProviderPublicKey) bool)
}

type KeyAssignment struct {
	Store Store
}

func MakeKeyAssignment(store Store) KeyAssignment {
	return KeyAssignment{
		Store: store,
	}
}

func (ka *KeyAssignment) SetProviderPubKeyToConsumerPubKey(pk ProviderPublicKey, ck ConsumerPublicKey) error {
	if _, ok := ka.Store.GetConsumerPublicKeyToProviderPublicKey(ck); ok {
		return errors.New(`cannot reuse key which is in use or was recently in use`)
	}
	if _, ok := ka.Store.GetConsumerConsAddrToLastUpdateMemo(TMCryptoPublicKeyToConsAddr(ck)); ok {
		return errors.New(`cannot reuse key which is in use or was recently in use`)
	}
	pca := TMCryptoPublicKeyToConsAddr(pk)
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
func (ka *KeyAssignment) DeleteProviderKey(pca ProviderConsAddr) error {
	// Delete the current mapping from the consumer key to the provider key
	if ck, ok := ka.Store.GetProviderConsAddrToConsumerPublicKey(pca); ok {
		ka.Store.DelConsumerPublicKeyToProviderPublicKey(ck)
	}
	// Delete the current mapping from the provider key to the consumer key
	ka.Store.DelProviderConsAddrToConsumerPublicKey(pca)
	toDelete := []ConsumerConsAddr{}
	// Find all the consumer keys which were mapped to by the provider key
	// in order to delete them
	ka.Store.IterateConsumerConsAddrToLastUpdateMemo(func(cca ConsumerConsAddr, lum providertypes.LastUpdateMemo) bool {
		pcaInMemo := TMCryptoPublicKeyToConsAddr(*lum.ProviderKey)
		if pca.Equals(pcaInMemo) {
			toDelete = append(toDelete, cca)
		}
		return false
	})
	// Delete the mappings from the consumer keys to the provider keys
	for _, cca := range toDelete {
		ka.Store.DelConsumerConsAddrToLastUpdateMemo(cca)
	}
	return nil
}

func (ka *KeyAssignment) GetCurrentConsumerPubKeyFromProviderPubKey(pk ProviderPublicKey) (ck ConsumerPublicKey, found bool) {
	return ka.Store.GetProviderConsAddrToConsumerPublicKey(TMCryptoPublicKeyToConsAddr(pk))
}

func (ka *KeyAssignment) GetProviderPubKeyFromConsumerPubKey(ck ConsumerPublicKey) (pk ProviderPublicKey, found bool) {
	return ka.Store.GetConsumerPublicKeyToProviderPublicKey(ck)
}

func (ka *KeyAssignment) GetProviderPubKeyFromConsumerConsAddress(cca sdk.ConsAddress) (pk ProviderPublicKey, found bool) {
	if lum, found := ka.Store.GetConsumerConsAddrToLastUpdateMemo(cca); found {
		return *lum.ProviderKey, true
	}
	return pk, false
}

func (ka *KeyAssignment) PruneUnusedKeys(latestVscid VSCID) {
	toDel := []ConsumerConsAddr{}
	ka.Store.IterateConsumerConsAddrToLastUpdateMemo(func(cca ConsumerConsAddr, lum providertypes.LastUpdateMemo) bool {
		if lum.Power == 0 && lum.Vscid <= latestVscid {
			toDel = append(toDel, cca)
		}
		return false
	})
	for _, cca := range toDel {
		ka.Store.DelConsumerConsAddrToLastUpdateMemo(cca)
	}
}

func (ka *KeyAssignment) getProviderKeysForUpdate(stakingUpdates map[ProviderPublicKey]int64) ([]ProviderPublicKey, map[string]bool) {

	// Return a list of provider keys that need to be updated
	keys := []ProviderPublicKey{}
	// Key types cannot be used for map lookup so use this string indexed
	// map to check if a key is already in the list
	included := map[string]bool{}

	// Get provider keys which the consumer is aware of, because the
	// last update sent to the consumer was a positive power update
	// and the assigned key has changed since that update.
	ka.Store.IterateConsumerConsAddrToLastUpdateMemo(func(cca ConsumerConsAddr, lum providertypes.LastUpdateMemo) bool {
		pca := TMCryptoPublicKeyToConsAddr(*lum.ProviderKey)
		if newCk, ok := ka.Store.GetProviderConsAddrToConsumerPublicKey(pca); ok {
			oldCk := lum.ConsumerKey
			if !oldCk.Equal(newCk) && 0 < lum.Power {
				keys = append(keys, *lum.ProviderKey)
				included[DeterministicStringify(*lum.ProviderKey)] = true
			}
		}
		return false
	})

	// Get provider keys where the validator power has changed
	for providerPublicKey := range stakingUpdates {
		s := DeterministicStringify(providerPublicKey)
		if !included[s] {
			keys = append(keys, providerPublicKey)
			included[s] = true
		}
	}

	return keys, included
}

func (ka KeyAssignment) getProviderKeysLastPositiveUpdate(mustCreateUpdate map[string]bool) map[string]providertypes.LastUpdateMemo {
	lastUpdate := map[string]providertypes.LastUpdateMemo{}
	ka.Store.IterateConsumerConsAddrToLastUpdateMemo(func(_ ConsumerConsAddr, lum providertypes.LastUpdateMemo) bool {
		s := DeterministicStringify(*lum.ProviderKey)
		if 0 < lum.Power {
			if _, found := mustCreateUpdate[s]; found {
				lastUpdate[s] = lum
			}
		}
		return false
	})
	return lastUpdate
}

// do inner work as part of ComputeUpdates
func (ka *KeyAssignment) getConsumerUpdates(vscid VSCID, stakingUpdates map[ProviderPublicKey]int64) (consumerUpdates map[ConsumerPublicKey]int64) {

	// Init the return value
	consumerUpdates = map[ConsumerPublicKey]int64{}

	providerKeysForUpdate, mustUpdate := ka.getProviderKeysForUpdate(stakingUpdates)
	providerKeysLastPositivePowerUpdateMemo := ka.getProviderKeysLastPositiveUpdate(mustUpdate)

	canonicalConsumerKey := map[string]ConsumerPublicKey{}

	/*
		Create a deletion (zero power) update for any consumer key known to the consumer
		that is no longer in use, or for which the power has changed.
	*/
	for i := range providerKeysForUpdate {
		// For each provider key for which there was already a positive update
		// create a deletion update for the associated consumer key.
		pk := providerKeysForUpdate[i] // Avoid taking address to loop variable
		if lum, found := providerKeysLastPositivePowerUpdateMemo[DeterministicStringify(pk)]; found {
			s := DeterministicStringify(*lum.ConsumerKey)
			canonicalConsumerKey[s] = *lum.ConsumerKey
			consumerUpdates[*lum.ConsumerKey] = 0
			cca := TMCryptoPublicKeyToConsAddr(*lum.ConsumerKey)
			ka.Store.SetConsumerConsAddrToLastUpdateMemo(cca, providertypes.LastUpdateMemo{ConsumerKey: lum.ConsumerKey, ProviderKey: &pk, Vscid: vscid, Power: 0})
		}
	}

	/*
		Create a positive power update for any consumer key which is in use.
	*/
	for i := range providerKeysForUpdate {
		pk := providerKeysForUpdate[i] // Avoid taking address to loop variable

		// For each provider key where there was either
		// 1) already a positive power update
		// 2) the validator power has changed (and is positive)
		// create a change update for the associated consumer key.

		var power int64 = 0

		if lum, found := providerKeysLastPositivePowerUpdateMemo[DeterministicStringify(pk)]; found {
			// There was previously a positive power update: copy it.
			power = lum.Power
		}

		// There is a new validator power: use it. It takes precedence.
		if updatedVotingPower, ok := stakingUpdates[pk]; ok {
			power = updatedVotingPower
		}

		// Only ship update with positive powers.
		if 0 < power {
			ck, found := ka.Store.GetProviderConsAddrToConsumerPublicKey(TMCryptoPublicKeyToConsAddr(pk))
			if !found {
				panic("must find ck for pk")
			}
			cca := TMCryptoPublicKeyToConsAddr(ck)
			ka.Store.SetConsumerConsAddrToLastUpdateMemo(cca, providertypes.LastUpdateMemo{ConsumerKey: &ck, ProviderKey: &pk, Vscid: vscid, Power: power})
			if k, found := canonicalConsumerKey[DeterministicStringify(ck)]; found {
				consumerUpdates[k] = power
			} else {
				consumerUpdates[ck] = power
			}
		}
	}

	return consumerUpdates
}

func toMap(providerUpdates []abci.ValidatorUpdate) map[ProviderPublicKey]int64 {
	ret := map[ProviderPublicKey]int64{}
	for _, u := range providerUpdates {
		ret[u.PubKey] = u.Power
	}
	return ret
}

func fromMap(consumerUpdates map[ConsumerPublicKey]int64) []abci.ValidatorUpdate {
	ret := []abci.ValidatorUpdate{}
	for ck, power := range consumerUpdates {
		ret = append(ret, abci.ValidatorUpdate{PubKey: ck, Power: power})
	}
	sort.Slice(ret, func(i, j int) bool {
		if ret[i].Power > ret[j].Power {
			return true
		}
		return ret[i].PubKey.String() > ret[j].PubKey.String()
	})
	return ret
}

func (ka *KeyAssignment) ComputeUpdates(vscid VSCID, stakingUpdates []abci.ValidatorUpdate) (consumerUpdates []abci.ValidatorUpdate) {
	return fromMap(ka.getConsumerUpdates(vscid, toMap(stakingUpdates)))
}

func (ka *KeyAssignment) AssignDefaultsForProviderKeysWithoutExplicitAssignments(updates []abci.ValidatorUpdate) {
	for _, u := range updates {
		if _, found := ka.GetCurrentConsumerPubKeyFromProviderPubKey(u.PubKey); !found {
			// The provider has not designated a key to use for the consumer chain. Use the provider key
			// by default.
			_ = ka.SetProviderPubKeyToConsumerPubKey(u.PubKey, u.PubKey)
		}
	}
}

func (ka *KeyAssignment) AssignDefaultsAndComputeUpdates(vscid VSCID, stakingUpdates []abci.ValidatorUpdate) (consumerUpdates []abci.ValidatorUpdate) {
	ka.AssignDefaultsForProviderKeysWithoutExplicitAssignments(stakingUpdates)
	return ka.ComputeUpdates(vscid, stakingUpdates)
}

// Returns true iff internal invariants hold
func (ka *KeyAssignment) InternalInvariants() bool {

	good := true

	{
		// No two provider keys can map to the same consumer key
		// (ProviderConsAddrToConsumerPublicKey is sane)
		seen := map[string]bool{}
		ka.Store.IterateProviderConsAddrToConsumerPublicKey(func(_ ProviderConsAddr, ck ConsumerPublicKey) bool {
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
		ka.Store.IterateProviderConsAddrToConsumerPublicKey(func(pca ProviderConsAddr, ck ConsumerPublicKey) bool {
			if pkQueried, ok := ka.Store.GetConsumerPublicKeyToProviderPublicKey(ck); ok {
				pcaQueried := TMCryptoPublicKeyToConsAddr(pkQueried)
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
		ka.Store.IterateConsumerPublicKeyToProviderPublicKey(func(ck ConsumerPublicKey, _ ProviderPublicKey) bool {
			found := false
			ka.Store.IterateProviderConsAddrToConsumerPublicKey(func(_ ProviderConsAddr, candidateCk ConsumerPublicKey) bool {
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
		ka.Store.IterateConsumerPublicKeyToProviderPublicKey(func(ck ConsumerPublicKey, pk ProviderPublicKey) bool {
			if m, ok := ka.Store.GetConsumerConsAddrToLastUpdateMemo(TMCryptoPublicKeyToConsAddr(ck)); ok {
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
		ka.Store.IterateConsumerConsAddrToLastUpdateMemo(func(cca ConsumerConsAddr, lum providertypes.LastUpdateMemo) bool {
			consAddr := TMCryptoPublicKeyToConsAddr(*lum.ConsumerKey)
			good = good && cca.Equals(consAddr)
			return false
		})
	}

	{
		// The set of all LastUpdateMemos with positive power
		// has pairwise unique provider keys
		seen := map[string]bool{}
		ka.Store.IterateConsumerConsAddrToLastUpdateMemo(func(_ ConsumerConsAddr, lum providertypes.LastUpdateMemo) bool {
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

func (s *KeyAssignmentStore) SetProviderConsAddrToConsumerPublicKey(k ProviderConsAddr, v ConsumerPublicKey) {
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

func (s *KeyAssignmentStore) SetConsumerPublicKeyToProviderPublicKey(k ConsumerPublicKey, v ProviderPublicKey) {
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

func (s *KeyAssignmentStore) SetConsumerConsAddrToLastUpdateMemo(k ConsumerConsAddr, v providertypes.LastUpdateMemo) {
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

func (s *KeyAssignmentStore) GetProviderConsAddrToConsumerPublicKey(k ProviderConsAddr) (v ConsumerPublicKey, found bool) {
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

func (s *KeyAssignmentStore) GetConsumerPublicKeyToProviderPublicKey(k ConsumerPublicKey) (v ProviderPublicKey, found bool) {
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

func (s *KeyAssignmentStore) GetConsumerConsAddrToLastUpdateMemo(k ConsumerConsAddr) (v providertypes.LastUpdateMemo, found bool) {
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

func (s *KeyAssignmentStore) DelProviderConsAddrToConsumerPublicKey(k ProviderConsAddr) {
	kbz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	s.Store.Delete(providertypes.KeyAssignmentProviderConsAddrToConsumerPublicKeyKey(s.ChainID, kbz))
}

func (s *KeyAssignmentStore) DelConsumerPublicKeyToProviderPublicKey(k ConsumerPublicKey) {
	kbz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	s.Store.Delete(providertypes.KeyAssignmentConsumerPublicKeyToProviderPublicKeyKey(s.ChainID, kbz))
}

func (s *KeyAssignmentStore) DelConsumerConsAddrToLastUpdateMemo(k ConsumerConsAddr) {
	kbz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	s.Store.Delete(providertypes.KeyAssignmentConsumerConsAddrToLastUpdateMemoKey(s.ChainID, kbz))
}

func (s *KeyAssignmentStore) IterateProviderConsAddrToConsumerPublicKey(cb func(ProviderConsAddr, ConsumerPublicKey) bool) {
	prefix := providertypes.KeyAssignmentProviderConsAddrToConsumerPublicKeyChainPrefix(s.ChainID)
	iterator := sdk.KVStorePrefixIterator(s.Store, prefix)
	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		k := ProviderConsAddr{}
		err := k.Unmarshal(iterator.Key()[len(prefix):])
		if err != nil {
			panic(err)
		}
		v := ConsumerPublicKey{}
		err = v.Unmarshal(iterator.Value())
		if err != nil {
			panic(err)
		}
		if cb(k, v) {
			return
		}
	}
}

func (s *KeyAssignmentStore) IterateConsumerPublicKeyToProviderPublicKey(cb func(ConsumerPublicKey, ProviderPublicKey) bool) {
	prefix := providertypes.KeyAssignmentConsumerPublicKeyToProviderPublicKeyChainPrefix(s.ChainID)
	iterator := sdk.KVStorePrefixIterator(s.Store, prefix)
	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		k := ConsumerPublicKey{}
		err := k.Unmarshal(iterator.Key()[len(prefix):])
		if err != nil {
			panic(err)
		}
		v := ProviderPublicKey{}
		err = v.Unmarshal(iterator.Value())
		if err != nil {
			panic(err)
		}
		if cb(k, v) {
			return
		}
	}
}

func (s *KeyAssignmentStore) IterateConsumerConsAddrToLastUpdateMemo(cb func(ConsumerConsAddr, providertypes.LastUpdateMemo) bool) {
	prefix := providertypes.KeyAssignmentConsumerConsAddrToLastUpdateMemoChainPrefix(s.ChainID)
	iterator := sdk.KVStorePrefixIterator(s.Store, prefix)
	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		k := ConsumerConsAddr{}
		err := k.Unmarshal(iterator.Key()[len(prefix):])
		if err != nil {
			panic(err)
		}
		v := providertypes.LastUpdateMemo{}
		err = v.Unmarshal(iterator.Value())
		if err != nil {
			panic(err)
		}
		if cb(k, v) {
			return
		}
	}
}

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
func (k Keeper) GetProviderConsAddrForSlashing(ctx sdk.Context, chainID string, data ccv.SlashPacketData) (sdk.ConsAddress, error) {
	consumerConsAddr := sdk.ConsAddress(data.Validator.Address)
	providerPublicKey, found := k.KeyAssignment(ctx, chainID).GetProviderPubKeyFromConsumerConsAddress(consumerConsAddr)
	if !found {
		// It is possible for a faulty consumer chain to send a slash packet for a validator that does
		// not have a key assignment on the provider chain. In this case, we do not slash the validator
		// and do not panic.
		return nil, errors.New("could not find provider address for slashing")
	}
	return TMCryptoPublicKeyToConsAddr(providerPublicKey), nil
}

func (k Keeper) KeyAssignment(ctx sdk.Context, chainID string) *KeyAssignment {
	store := KeyAssignmentStore{ctx.KVStore(k.storeKey), chainID}
	ka := MakeKeyAssignment(&store)
	return &ka
}
