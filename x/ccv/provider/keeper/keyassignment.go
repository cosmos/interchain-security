package keeper

import (
	"errors"

	sdk "github.com/cosmos/cosmos-sdk/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"

	sdkcryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"

	abci "github.com/tendermint/tendermint/abci/types"

	tmprotocrypto "github.com/tendermint/tendermint/proto/tendermint/crypto"
)

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

func PubKeyToConsAddr(k tmprotocrypto.PublicKey) sdk.ConsAddress {
	sdkK, err := sdkcryptocodec.FromTmProtoPublicKey(k)
	if err != nil {
		panic("could not get public key from tm proto public key")
	}
	return sdk.GetConsAddress(sdkK)
}

type Store interface {
	SetProviderConsAddrToConsumerPublicKey(ProviderConsAddr, ConsumerPublicKey)
	SetConsumerPublicKeyToProviderPublicKey(ConsumerPublicKey, ProviderPublicKey)
	SetConsumerConsAddrToLastUpdateMemo(ConsumerConsAddr, providertypes.LastUpdateMemo)
	GetProviderConsAddrToConsumerPublicKey(ProviderConsAddr) (ConsumerPublicKey, bool)
	GetConsumerPublicKeyToProviderPublicKey(ConsumerPublicKey) (ProviderPublicKey, bool)
	GetConsumerConsAddrToLastUpdateMemo(ConsumerConsAddr) (providertypes.LastUpdateMemo, bool)
	DelProviderConsAddrToConsumerPublicKey(ProviderConsAddr)
	DelConsumerPublicKeyToProviderPublicKey(ConsumerPublicKey)
	DelConsumerConsAddrToLastUpdateMemo(ConsumerConsAddr)
	IterateProviderConsAddrToConsumerPublicKey(func(ProviderConsAddr, ConsumerPublicKey) bool)
	IterateConsumerPublicKeyToProviderPublicKey(func(ConsumerPublicKey, ProviderPublicKey) bool)
	IterateConsumerConsAddrToLastUpdateMemo(func(ConsumerConsAddr, providertypes.LastUpdateMemo) bool)
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
	if _, ok := ka.Store.GetConsumerConsAddrToLastUpdateMemo(PubKeyToConsAddr(ck)); ok {
		return errors.New(`cannot reuse key which is in use or was recently in use`)
	}
	pca := PubKeyToConsAddr(pk)
	if oldCk, ok := ka.Store.GetProviderConsAddrToConsumerPublicKey(pca); ok {
		ka.Store.DelConsumerPublicKeyToProviderPublicKey(oldCk)
	}
	ka.Store.SetProviderConsAddrToConsumerPublicKey(pca, ck)
	ka.Store.SetConsumerPublicKeyToProviderPublicKey(ck, pk)
	return nil
}

func (ka *KeyAssignment) DeleteProviderKey(pca ProviderConsAddr) error {
	// TODO: document expensive operation
	if ck, ok := ka.Store.GetProviderConsAddrToConsumerPublicKey(pca); ok {
		ka.Store.DelConsumerPublicKeyToProviderPublicKey(ck)
	}
	ka.Store.DelProviderConsAddrToConsumerPublicKey(pca)
	toDelete := []ConsumerConsAddr{}
	ka.Store.IterateConsumerConsAddrToLastUpdateMemo(func(cca ConsumerConsAddr, lum providertypes.LastUpdateMemo) bool {
		pcaInMemo := PubKeyToConsAddr(*lum.ProviderKey)
		if pca.Equals(pcaInMemo) { // TODO: find other place where I should have used Equals
			toDelete = append(toDelete, cca)
		}
		return false
	})
	for _, cca := range toDelete {
		ka.Store.DelConsumerConsAddrToLastUpdateMemo(cca)
	}
	return nil
}

func (ka *KeyAssignment) GetCurrentConsumerPubKeyFromProviderPubKey(pk ProviderPublicKey) (ck ConsumerPublicKey, found bool) {
	return ka.Store.GetProviderConsAddrToConsumerPublicKey(PubKeyToConsAddr(pk))
}

func (ka *KeyAssignment) GetProviderPubKeyFromConsumerPubKey(ck ConsumerPublicKey) (pk ProviderPublicKey, found bool) {
	return ka.Store.GetConsumerPublicKeyToProviderPublicKey(ck)
}

func (ka *KeyAssignment) GetProviderPubKeyFromConsumerConsAddress(cca sdk.ConsAddress) (pk ProviderPublicKey, found bool) {
	if memo, found := ka.Store.GetConsumerConsAddrToLastUpdateMemo(cca); found {
		return *memo.ProviderKey, true
	}
	return pk, false
}

func (ka *KeyAssignment) PruneUnusedKeys(latestVscid VSCID) {
	toDel := []ConsumerConsAddr{}
	ka.Store.IterateConsumerConsAddrToLastUpdateMemo(func(cca ConsumerConsAddr, m providertypes.LastUpdateMemo) bool {
		if m.Power == 0 && m.Vscid <= latestVscid {
			toDel = append(toDel, cca)
		}
		return false
	})
	for _, cca := range toDel {
		ka.Store.DelConsumerConsAddrToLastUpdateMemo(cca)
	}
}

func (ka *KeyAssignment) getProviderKeysForUpdate(stakingUpdates map[ProviderPublicKey]int64) ([]ProviderPublicKey, map[string]bool) {

	// TODO: document
	keys := []ProviderPublicKey{}
	included := map[string]bool{}

	// Get provider keys which the consumer is aware of, because the
	// last update sent to the consumer was a positive power update
	// and the assigned key has changed since that update.
	ka.Store.IterateConsumerConsAddrToLastUpdateMemo(func(cca ConsumerConsAddr, m providertypes.LastUpdateMemo) bool {
		pca := PubKeyToConsAddr(*m.ProviderKey)
		if newCk, ok := ka.Store.GetProviderConsAddrToConsumerPublicKey(pca); ok { // TODO: do away with ok, should always be ok
			oldCk := m.ConsumerKey
			if !oldCk.Equal(newCk) && 0 < m.Power {
				keys = append(keys, *m.ProviderKey)
				included[DeterministicStringify(*m.ProviderKey)] = true
			}
		}
		return false
	})

	// Get provider keys where the validator power has changed
	for pk := range stakingUpdates {
		s := DeterministicStringify(pk)
		if !included[s] {
			keys = append(keys, pk)
			included[s] = true
		}
	}

	return keys, included
}

func (ka KeyAssignment) getProviderKeysLastPositiveUpdate(mustCreateUpdate map[string]bool) map[string]providertypes.LastUpdateMemo {
	lastUpdate := map[string]providertypes.LastUpdateMemo{}
	ka.Store.IterateConsumerConsAddrToLastUpdateMemo(func(_ ConsumerConsAddr, m providertypes.LastUpdateMemo) bool {
		s := DeterministicStringify(*m.ProviderKey)
		if 0 < m.Power {
			if _, found := mustCreateUpdate[s]; found {
				lastUpdate[s] = m
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
	providerKeysLastPositivePowerUpdate := ka.getProviderKeysLastPositiveUpdate(mustUpdate)

	canonicalConsumerKey := map[string]ConsumerPublicKey{}

	/*
		Create a deletion (zero power) update for any consumer key known to the consumer
		that is no longer in use, or for which the power has changed.
	*/
	for i := range providerKeysForUpdate {
		// For each provider key for which there was already a positive update
		// create a deletion update for the associated consumer key.
		pk := providerKeysForUpdate[i]
		if u, found := providerKeysLastPositivePowerUpdate[DeterministicStringify(pk)]; found {
			s := DeterministicStringify(*u.ConsumerKey)
			canonicalConsumerKey[s] = *u.ConsumerKey
			consumerUpdates[*u.ConsumerKey] = 0
			cca := PubKeyToConsAddr(*u.ConsumerKey)
			ka.Store.SetConsumerConsAddrToLastUpdateMemo(cca, providertypes.LastUpdateMemo{ConsumerKey: u.ConsumerKey, ProviderKey: &pk, Vscid: vscid, Power: 0})
		}
	}

	/*
		Create a positive power update for any consumer key which is in use.
	*/
	for i := range providerKeysForUpdate {
		pk := providerKeysForUpdate[i]
		// For each provider key where there was either
		// 1) already a positive power update
		// 2) the validator power has changed (and is positive)
		// create a change update for the associated consumer key.

		var power int64 = 0

		if u, found := providerKeysLastPositivePowerUpdate[DeterministicStringify(pk)]; found {
			// There was previously a positive power update: copy it.
			power = u.Power
		}

		// There is a new validator power: use it. It takes precedence.
		if newPower, ok := stakingUpdates[pk]; ok {
			power = newPower
		}

		// Only ship update with positive powers.
		if 0 < power {
			ck, found := ka.Store.GetProviderConsAddrToConsumerPublicKey(PubKeyToConsAddr(pk))
			if !found {
				panic("must find ck for pk")
			}
			cca := PubKeyToConsAddr(ck)
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
	// TODO: add panic
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
	return ret
}

func (ka *KeyAssignment) ComputeUpdates(vscid VSCID, stakingUpdates []abci.ValidatorUpdate) (consumerUpdatesx []abci.ValidatorUpdate) {
	return fromMap(ka.getConsumerUpdates(vscid, toMap(stakingUpdates)))
}

// Returns true iff internal invariants hold
func (ka *KeyAssignment) InternalInvariants() bool {

	good := true

	{
		// No two provider keys can map to the same consumer key
		// (pkToCk is sane)
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
		// All values of pkToCk is a key of ckToPk
		// (reverse lookup is always possible)
		ka.Store.IterateProviderConsAddrToConsumerPublicKey(func(pca ProviderConsAddr, ck ConsumerPublicKey) bool {
			if pkQueried, ok := ka.Store.GetConsumerPublicKeyToProviderPublicKey(ck); ok {
				pcaQueried := PubKeyToConsAddr(pkQueried)
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
		// any memo containing the same consumer key has the same
		// mapping.
		// (Ensures lookups are correct)
		ka.Store.IterateConsumerPublicKeyToProviderPublicKey(func(ck ConsumerPublicKey, pk ProviderPublicKey) bool {
			if m, ok := ka.Store.GetConsumerConsAddrToLastUpdateMemo(PubKeyToConsAddr(ck)); ok {
				if !pk.Equal(m.ProviderKey) {
					good = false
				}
			}
			return false
		})
	}

	{
		// All entries in ckToMemo have a consumer consensus
		// address which is the address held inside
		ka.Store.IterateConsumerConsAddrToLastUpdateMemo(func(cca ConsumerConsAddr, m providertypes.LastUpdateMemo) bool {
			cons := PubKeyToConsAddr(*m.ConsumerKey)
			if len(cca) != len(cons) {
				good = false
			}
			for i := range cons {
				if cons[i] != cca[i] {
					good = false
				}
			}
			return false
		})
	}

	{
		// The set of all LastUpdateMemos with positive power
		// has pairwise unique provider keys
		seen := map[string]bool{}
		ka.Store.IterateConsumerConsAddrToLastUpdateMemo(func(_ ConsumerConsAddr, m providertypes.LastUpdateMemo) bool {
			if 0 < m.Power {
				s := DeterministicStringify(*m.ProviderKey)
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
	s.Store.Set(providertypes.KeyAssignmentPcaToCkKey(s.ChainID, kbz), vbz)
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
	s.Store.Set(providertypes.KeyAssignmentCkToPkKey(s.ChainID, kbz), vbz)
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
	s.Store.Set(providertypes.KeyAssignmentCcaToLastUpdateMemoKey(s.ChainID, kbz), vbz)
}
func (s *KeyAssignmentStore) GetProviderConsAddrToConsumerPublicKey(k ProviderConsAddr) (v ConsumerPublicKey, found bool) {
	kbz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	if vbz := s.Store.Get(providertypes.KeyAssignmentPcaToCkKey(s.ChainID, kbz)); vbz != nil {
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
	if vbz := s.Store.Get(providertypes.KeyAssignmentCkToPkKey(s.ChainID, kbz)); vbz != nil {
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
	if vbz := s.Store.Get(providertypes.KeyAssignmentCcaToLastUpdateMemoKey(s.ChainID, kbz)); vbz != nil {
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
	s.Store.Delete(providertypes.KeyAssignmentPcaToCkKey(s.ChainID, kbz))
}
func (s *KeyAssignmentStore) DelConsumerPublicKeyToProviderPublicKey(k ConsumerPublicKey) {
	kbz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	s.Store.Delete(providertypes.KeyAssignmentCkToPkKey(s.ChainID, kbz))
}
func (s *KeyAssignmentStore) DelConsumerConsAddrToLastUpdateMemo(k ConsumerConsAddr) {
	kbz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	s.Store.Delete(providertypes.KeyAssignmentCcaToLastUpdateMemoKey(s.ChainID, kbz))
}
func (s *KeyAssignmentStore) IterateProviderConsAddrToConsumerPublicKey(cb func(ProviderConsAddr, ConsumerPublicKey) bool) {
	prefix := providertypes.KeyAssignmentPcaToCkChainPrefix(s.ChainID)
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
	prefix := providertypes.KeyAssignmentCkToPkChainPrefix(s.ChainID)
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
	prefix := providertypes.KeyAssignmentCcaToLastUpdateMemoChainPrefix(s.ChainID)
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
		providertypes.KeyAssignmentPcaToCkChainPrefix(chainID),
		providertypes.KeyAssignmentCkToPkChainPrefix(chainID),
		providertypes.KeyAssignmentCcaToLastUpdateMemoChainPrefix(chainID),
	} {
		iter := sdk.KVStorePrefixIterator(store, pref)
		defer iter.Close()
		for ; iter.Valid(); iter.Next() {
			store.Delete(iter.Key())
		}
	}
}

func (k Keeper) KeyAssignment(ctx sdk.Context, chainID string) *KeyAssignment {
	store := KeyAssignmentStore{ctx.KVStore(k.storeKey), chainID}
	ka := MakeKeyAssignment(&store)
	return &ka
}
