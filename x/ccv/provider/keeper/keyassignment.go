package keeper

import (
	"errors"

	sdk "github.com/cosmos/cosmos-sdk/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"

	sdkcryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"

	abci "github.com/tendermint/tendermint/abci/types"

	tmprotocrypto "github.com/tendermint/tendermint/proto/tendermint/crypto"
)

/*

   Rough thoughts

   ## Feature list

   - [ ] sendUpdate must work
   - [ ] slash requests must work
   - [ ] slash acks must work
   - [ ] pruning must work
   - [ ] mappings must to be present whenever a consumer genesis is created
   - [ ] consumer mappings must be deleted whenever a consumer is stopped/deleted
   - [ ] all mappings must be saved whenever the provider genesis is created
   - [ ] all mappings must be loaded whenever the provider is started from genesis (check this)
   - [ ] default mapping should be inserted whenever a validator update goes out for a previously unseen validator
   - [ ] it must be possible to change a mapping via a tx submitted to the provider
   - [ ] it must be possible to query current mappings (via rpc? how?)
   - [ ] garbage collect pkToCk, ckToPk if appropriate, when validator is destroyed
   - [ ] when a validator is destroyed all the memos that refer to it must be destroyed


   ## Quality list

   - [ ] check coverage
   - [ ] make sure all tests are included in coverage computation
   - [ ] make sure package org is sensible and things that should be
   - [ ] make sure private things are private
   - [ ] make sure public things are public
   - [ ] make sure diff tests (core) include a default mapping
   - [ ] ideally, use custom mappings in diff tests (core)
   - [ ] unit tests
   - [ ] fuzzing for serialization ?
   - [ ] use sdk idioms where appropriate
   	- [ ] PrefixStore
   - [ ] not too short var names
   - [ ] use 'KeyDesignation' as name?

   Memory trigger
   I have tackled a lot of the above but the integration points still aren't well tested.
   The things I need to do are to continue working outwards, testing as necessary. Some things are not implemented at all,
   these are
   	- [ ] tx's
   	- [ ] queries
   	- [1/2] consumer genesis
   		For this I think it is sufficient to map through any defaults, just as in SendValidatorUpdates
   		and call ComputeUpdates with a 0 vscid. This should allow future pruning.
		I think I've half completed this
   	- [x] provider genesis / init from genesis
   	- [ ] consumer removal
	- [ ] validator destruction (...?)
	- [x] diff test basic
	- [ ] diff test with random key assignments
		-

Current testing status
	All unit tests pass
	diff tests pass
	integration tests : ?

*/

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
	SetPcaToCk(ProviderConsAddr, ConsumerPublicKey)
	SetCkToPk(ConsumerPublicKey, ProviderPublicKey)
	SetCcaToLastUpdateMemo(ConsumerConsAddr, ccvtypes.LastUpdateMemo)
	GetPcaToCk(ProviderConsAddr) (ConsumerPublicKey, bool)
	GetCkToPk(ConsumerPublicKey) (ProviderPublicKey, bool)
	GetCcaToLastUpdateMemo(ConsumerConsAddr) (ccvtypes.LastUpdateMemo, bool)
	DelPcaToCk(ProviderConsAddr)
	DelCkToPk(ConsumerPublicKey)
	DelCcaToLastUpdateMemo(ConsumerConsAddr)
	IteratePcaToCk(func(ProviderConsAddr, ConsumerPublicKey) bool)
	IterateCkToPk(func(ConsumerPublicKey, ProviderPublicKey) bool)
	IterateCcaToLastUpdateMemo(func(ConsumerConsAddr, ccvtypes.LastUpdateMemo) bool)
}

type KeyAssignment struct {
	Store Store
}

func MakeKeyAssignment(store Store) KeyAssignment {
	return KeyAssignment{
		Store: store,
	}
}

func (e *KeyAssignment) SetProviderPubKeyToConsumerPubKey(pk ProviderPublicKey, ck ConsumerPublicKey) error {
	if _, ok := e.Store.GetCkToPk(ck); ok {
		return errors.New(`cannot reuse key which is in use or was recently in use`)
	}
	if _, ok := e.Store.GetCcaToLastUpdateMemo(PubKeyToConsAddr(ck)); ok {
		return errors.New(`cannot reuse key which is in use or was recently in use`)
	}
	pca := PubKeyToConsAddr(pk)
	if oldCk, ok := e.Store.GetPcaToCk(pca); ok {
		e.Store.DelCkToPk(oldCk)
	}
	e.Store.SetPcaToCk(pca, ck)
	e.Store.SetCkToPk(ck, pk)
	return nil
}

func (e *KeyAssignment) DeleteProviderKey(pca ProviderConsAddr) error {
	// TODO: document expensive operation
	if ck, ok := e.Store.GetPcaToCk(pca); ok {
		e.Store.DelCkToPk(ck)
	}
	e.Store.DelPcaToCk(pca)
	toDelete := []ConsumerConsAddr{}
	e.Store.IterateCcaToLastUpdateMemo(func(cca ConsumerConsAddr, lum ccvtypes.LastUpdateMemo) bool {
		pcaInMemo := PubKeyToConsAddr(*lum.ProviderKey)
		if pca.Equals(pcaInMemo) { // TODO: find other place where I should have used Equals
			toDelete = append(toDelete, cca)
		}
		return false
	})
	for _, cca := range toDelete {
		e.Store.DelCcaToLastUpdateMemo(cca)
	}
	return nil
}

func (e *KeyAssignment) GetCurrentConsumerPubKeyFromProviderPubKey(pk ProviderPublicKey) (ck ConsumerPublicKey, found bool) {
	return e.Store.GetPcaToCk(PubKeyToConsAddr(pk))
}

func (e *KeyAssignment) GetProviderPubKeyFromConsumerPubKey(ck ConsumerPublicKey) (pk ProviderPublicKey, found bool) {
	return e.Store.GetCkToPk(ck)
}

func (e *KeyAssignment) GetProviderPubKeyFromConsumerConsAddress(cca sdk.ConsAddress) (pk ProviderPublicKey, found bool) {
	if memo, found := e.Store.GetCcaToLastUpdateMemo(cca); found {
		return *memo.ProviderKey, true
	}
	return pk, false
}

func (e *KeyAssignment) PruneUnusedKeys(latestVscid VSCID) {
	toDel := []ConsumerConsAddr{}
	e.Store.IterateCcaToLastUpdateMemo(func(cca ConsumerConsAddr, m ccvtypes.LastUpdateMemo) bool {
		if m.Power == 0 && m.Vscid <= latestVscid {
			toDel = append(toDel, cca)
		}
		return false
	})
	for _, cca := range toDel {
		e.Store.DelCcaToLastUpdateMemo(cca)
	}
}

func (e *KeyAssignment) getProviderKeysForUpdate(stakingUpdates map[ProviderPublicKey]int64) ([]ProviderPublicKey, map[string]bool) {

	// TODO: document
	keys := []ProviderPublicKey{}
	included := map[string]bool{}

	// Get provider keys which the consumer is aware of, because the
	// last update sent to the consumer was a positive power update
	// and the assigned key has changed since that update.
	e.Store.IterateCcaToLastUpdateMemo(func(cca ConsumerConsAddr, m ccvtypes.LastUpdateMemo) bool {
		pca := PubKeyToConsAddr(*m.ProviderKey)
		if newCk, ok := e.Store.GetPcaToCk(pca); ok { // TODO: do away with ok, should always be ok
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

func (e KeyAssignment) getProviderKeysLastPositiveUpdate(mustCreateUpdate map[string]bool) map[string]ccvtypes.LastUpdateMemo {
	lastUpdate := map[string]ccvtypes.LastUpdateMemo{}
	e.Store.IterateCcaToLastUpdateMemo(func(_ ConsumerConsAddr, m ccvtypes.LastUpdateMemo) bool {
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
func (e *KeyAssignment) getConsumerUpdates(vscid VSCID, stakingUpdates map[ProviderPublicKey]int64) (consumerUpdates map[ConsumerPublicKey]int64) {

	// Init the return value
	consumerUpdates = map[ConsumerPublicKey]int64{}

	providerKeysForUpdate, mustUpdate := e.getProviderKeysForUpdate(stakingUpdates)
	providerKeysLastPositivePowerUpdate := e.getProviderKeysLastPositiveUpdate(mustUpdate)

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
			e.Store.SetCcaToLastUpdateMemo(cca, ccvtypes.LastUpdateMemo{ConsumerKey: u.ConsumerKey, ProviderKey: &pk, Vscid: vscid, Power: 0})
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
			ck, found := e.Store.GetPcaToCk(PubKeyToConsAddr(pk))
			if !found {
				panic("must find ck for pk")
			}
			cca := PubKeyToConsAddr(ck)
			e.Store.SetCcaToLastUpdateMemo(cca, ccvtypes.LastUpdateMemo{ConsumerKey: &ck, ProviderKey: &pk, Vscid: vscid, Power: power})
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

func (e *KeyAssignment) ComputeUpdates(vscid VSCID, stakingUpdates []abci.ValidatorUpdate) (consumerUpdatesx []abci.ValidatorUpdate) {
	return fromMap(e.getConsumerUpdates(vscid, toMap(stakingUpdates)))
}

// Returns true iff internal invariants hold
func (e *KeyAssignment) InternalInvariants() bool {

	good := true

	{
		// No two provider keys can map to the same consumer key
		// (pkToCk is sane)
		seen := map[string]bool{}
		e.Store.IteratePcaToCk(func(_ ProviderConsAddr, ck ConsumerPublicKey) bool {
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
		e.Store.IteratePcaToCk(func(pca ProviderConsAddr, ck ConsumerPublicKey) bool {
			if pkQueried, ok := e.Store.GetCkToPk(ck); ok {
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
		e.Store.IterateCkToPk(func(ck ConsumerPublicKey, _ ProviderPublicKey) bool {
			found := false
			e.Store.IteratePcaToCk(func(_ ProviderConsAddr, candidateCk ConsumerPublicKey) bool {
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
		e.Store.IterateCkToPk(func(ck ConsumerPublicKey, pk ProviderPublicKey) bool {
			if m, ok := e.Store.GetCcaToLastUpdateMemo(PubKeyToConsAddr(ck)); ok {
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
		e.Store.IterateCcaToLastUpdateMemo(func(cca ConsumerConsAddr, m ccvtypes.LastUpdateMemo) bool {
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
		e.Store.IterateCcaToLastUpdateMemo(func(_ ConsumerConsAddr, m ccvtypes.LastUpdateMemo) bool {
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

func (s *KeyAssignmentStore) SetPcaToCk(k ProviderConsAddr, v ConsumerPublicKey) {
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
func (s *KeyAssignmentStore) SetCkToPk(k ConsumerPublicKey, v ProviderPublicKey) {
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
func (s *KeyAssignmentStore) SetCcaToLastUpdateMemo(k ConsumerConsAddr, v ccvtypes.LastUpdateMemo) {
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
func (s *KeyAssignmentStore) GetPcaToCk(k ProviderConsAddr) (v ConsumerPublicKey, found bool) {
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
func (s *KeyAssignmentStore) GetCkToPk(k ConsumerPublicKey) (v ProviderPublicKey, found bool) {
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
func (s *KeyAssignmentStore) GetCcaToLastUpdateMemo(k ConsumerConsAddr) (v ccvtypes.LastUpdateMemo, found bool) {
	kbz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	if vbz := s.Store.Get(providertypes.KeyAssignmentCcaToLastUpdateMemoKey(s.ChainID, kbz)); vbz != nil {
		v := ccvtypes.LastUpdateMemo{}
		err := v.Unmarshal(vbz)
		if err != nil {
			panic(err)
		}
		return v, true
	}
	return v, false
}
func (s *KeyAssignmentStore) DelPcaToCk(k ProviderConsAddr) {
	kbz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	s.Store.Delete(providertypes.KeyAssignmentPcaToCkKey(s.ChainID, kbz))
}
func (s *KeyAssignmentStore) DelCkToPk(k ConsumerPublicKey) {
	kbz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	s.Store.Delete(providertypes.KeyAssignmentCkToPkKey(s.ChainID, kbz))
}
func (s *KeyAssignmentStore) DelCcaToLastUpdateMemo(k ConsumerConsAddr) {
	kbz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	s.Store.Delete(providertypes.KeyAssignmentCcaToLastUpdateMemoKey(s.ChainID, kbz))
}
func (s *KeyAssignmentStore) IteratePcaToCk(cb func(ProviderConsAddr, ConsumerPublicKey) bool) {
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
func (s *KeyAssignmentStore) IterateCkToPk(cb func(ConsumerPublicKey, ProviderPublicKey) bool) {
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
func (s *KeyAssignmentStore) IterateCcaToLastUpdateMemo(cb func(ConsumerConsAddr, ccvtypes.LastUpdateMemo) bool) {
	prefix := providertypes.KeyAssignmentCcaToLastUpdateMemoChainPrefix(s.ChainID)
	iterator := sdk.KVStorePrefixIterator(s.Store, prefix)
	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		k := ConsumerConsAddr{}
		err := k.Unmarshal(iterator.Key()[len(prefix):])
		if err != nil {
			panic(err)
		}
		v := ccvtypes.LastUpdateMemo{}
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
	km := MakeKeyAssignment(&store)
	return &km
}
