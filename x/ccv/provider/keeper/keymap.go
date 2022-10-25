package keeper

import (
	"errors"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"

	abci "github.com/tendermint/tendermint/abci/types"

	crypto "github.com/tendermint/tendermint/proto/tendermint/crypto"
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
type ProviderPubKey = crypto.PublicKey
type ConsumerPubKey = crypto.PublicKey
type ConsumerConsAddr = sdk.ConsAddress

func DeterministicStringify(k crypto.PublicKey) string {
	bz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	return string(bz)
}

func ConsumerPubKeyToConsumerConsAddr(ck ConsumerPubKey) ConsumerConsAddr {
	sdkCk, err := cryptocodec.FromTmProtoPublicKey(ck)
	if err != nil {
		panic("could not get public key from tm proto public key")
	}
	return sdk.GetConsAddress(sdkCk)
}

type Store interface {
	SetPkToCk(ProviderPubKey, ConsumerPubKey)
	SetCkToPk(ConsumerPubKey, ProviderPubKey)
	SetCcaToLastUpdateMemo(ConsumerConsAddr, ccvtypes.LastUpdateMemo)
	GetPkToCk(ProviderPubKey) (ConsumerPubKey, bool)
	GetCkToPk(ConsumerPubKey) (ProviderPubKey, bool)
	GetCcaToLastUpdateMemo(ConsumerConsAddr) (ccvtypes.LastUpdateMemo, bool)
	DelPkToCk(ProviderPubKey)
	DelCkToPk(ConsumerPubKey)
	DelCcaToLastUpdateMemo(ConsumerConsAddr)
	IteratePkToCk(func(ProviderPubKey, ConsumerPubKey) bool)
	IterateCkToPk(func(ConsumerPubKey, ProviderPubKey) bool)
	IterateCcaToLastUpdateMemo(func(ConsumerConsAddr, ccvtypes.LastUpdateMemo) bool)
}

type KeyMap struct {
	Store Store
}

func MakeKeyMap(store Store) KeyMap {
	return KeyMap{
		Store: store,
	}
}

func (e *KeyMap) SetProviderPubKeyToConsumerPubKey(pk ProviderPubKey, ck ConsumerPubKey) error {
	if _, ok := e.Store.GetCkToPk(ck); ok {
		return errors.New(`cannot reuse key which is in use or was recently in use`)
	}
	if _, ok := e.Store.GetCcaToLastUpdateMemo(ConsumerPubKeyToConsumerConsAddr(ck)); ok {
		return errors.New(`cannot reuse key which is in use or was recently in use`)
	}
	if oldCk, ok := e.Store.GetPkToCk(pk); ok {
		e.Store.DelCkToPk(oldCk)
	}
	e.Store.SetPkToCk(pk, ck)
	e.Store.SetCkToPk(ck, pk)
	return nil
}

func (e *KeyMap) GetCurrentConsumerPubKeyFromProviderPubKey(pk ProviderPubKey) (ck ConsumerPubKey, found bool) {
	return e.Store.GetPkToCk(pk)
}

func (e *KeyMap) GetProviderPubKeyFromConsumerPubKey(ck ConsumerPubKey) (pk ProviderPubKey, found bool) {
	return e.Store.GetCkToPk(ck)
}

func (e *KeyMap) GetProviderPubKeyFromConsumerConsAddress(cca sdk.ConsAddress) (pk ProviderPubKey, found bool) {
	if memo, found := e.Store.GetCcaToLastUpdateMemo(cca); found {
		return *memo.Pk, true
	}
	return pk, false
}

func (e *KeyMap) PruneUnusedKeys(latestVscid VSCID) {
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

func toMap(providerUpdates []abci.ValidatorUpdate) map[ProviderPubKey]int64 {
	ret := map[ProviderPubKey]int64{}
	for _, u := range providerUpdates {
		ret[u.PubKey] = u.Power
	}
	return ret
}

func fromMap(consumerUpdates map[ConsumerPubKey]int64) []abci.ValidatorUpdate {
	ret := []abci.ValidatorUpdate{}
	for ck, power := range consumerUpdates {
		ret = append(ret, abci.ValidatorUpdate{PubKey: ck, Power: power})
	}
	return ret
}

func (e *KeyMap) ComputeUpdates(vscid VSCID, providerUpdates []abci.ValidatorUpdate) (consumerUpdatesx []abci.ValidatorUpdate) {
	return fromMap(e.getConsumerUpdates(vscid, toMap(providerUpdates)))
}

// do inner work as part of ComputeUpdates
func (e *KeyMap) getConsumerUpdates(vscid VSCID, providerUpdates map[ProviderPubKey]int64) (consumerUpdates map[ConsumerPubKey]int64) {

	providerKeysToSendUpdateFor := []ProviderPubKey{}
	keyInProviderKeysToSendUpdateFor := map[string]bool{}

	// Grab provider keys where the last update had positive power
	// and where the assigned consumer key has changed
	e.Store.IterateCcaToLastUpdateMemo(func(cca ConsumerConsAddr, m ccvtypes.LastUpdateMemo) bool {
		oldCk := m.Ck
		if newCk, ok := e.Store.GetPkToCk(*m.Pk); ok { // TODO: do away with ok, should always be ok
			// TODO: is !seen[str] needed?
			if !oldCk.Equal(newCk) && 0 < m.Power {
				providerKeysToSendUpdateFor = append(providerKeysToSendUpdateFor, *m.Pk)
				keyInProviderKeysToSendUpdateFor[DeterministicStringify(*m.Pk)] = true
			}
		}
		return false
	})

	// Grab provider keys where the validator power has changed
	for pk := range providerUpdates {
		str := DeterministicStringify(pk)
		if !keyInProviderKeysToSendUpdateFor[str] {
			providerKeysToSendUpdateFor = append(providerKeysToSendUpdateFor, pk)
			keyInProviderKeysToSendUpdateFor[str] = true
		}
	}

	providerKeysLastPositivePowerUpdate := map[string]ccvtypes.LastUpdateMemo{}
	canonicalKey := map[string]ConsumerPubKey{}
	consumerUpdates = map[ConsumerPubKey]int64{}

	e.Store.IterateCcaToLastUpdateMemo(func(_ ConsumerConsAddr, m ccvtypes.LastUpdateMemo) bool {
		str := DeterministicStringify(*m.Pk)
		if 0 < m.Power {
			if _, found := keyInProviderKeysToSendUpdateFor[str]; found {
				providerKeysLastPositivePowerUpdate[str] = m
			}
		}
		return false
	})

	for i := range providerKeysToSendUpdateFor {
		pk := providerKeysToSendUpdateFor[i]
		if u, found := providerKeysLastPositivePowerUpdate[DeterministicStringify(pk)]; found {
			// For each provider key for which there was already a positive update
			// create a deletion update for the associated consumer key.
			cca := ConsumerPubKeyToConsumerConsAddr(*u.Ck)
			e.Store.SetCcaToLastUpdateMemo(cca, ccvtypes.LastUpdateMemo{Ck: u.Ck, Pk: &pk, Vscid: vscid, Power: 0})
			consumerUpdates[*u.Ck] = 0
			canonicalKey[DeterministicStringify(*u.Ck)] = *u.Ck
		}
	}

	for i := range providerKeysToSendUpdateFor {
		pk := providerKeysToSendUpdateFor[i]
		// For each provider key where there was either
		// 1) already a positive power update
		// 2) the validator power has changed (and is positive)
		// create a change update for the associated consumer key.

		var power int64 = 0
		if u, found := providerKeysLastPositivePowerUpdate[DeterministicStringify(pk)]; found {
			// There was previously a positive power update: copy it.
			power = u.Power
		}

		// There is a new validator power: use it.
		if newPower, ok := providerUpdates[pk]; ok {
			power = newPower
		}
		// Only ship update with positive powers.
		if 0 < power {
			ck, found := e.Store.GetPkToCk(pk)
			if !found {
				panic("must find ck for pk")
			}
			cca := ConsumerPubKeyToConsumerConsAddr(ck)
			e.Store.SetCcaToLastUpdateMemo(cca, ccvtypes.LastUpdateMemo{Ck: &ck, Pk: &pk, Vscid: vscid, Power: power})
			if k, found := canonicalKey[DeterministicStringify(ck)]; found {
				consumerUpdates[k] = power
			} else {
				consumerUpdates[ck] = power
			}
		}
	}

	return consumerUpdates
}

// Returns true iff internal invariants hold
func (e *KeyMap) InternalInvariants() bool {

	good := true

	{
		// No two provider keys can map to the same consumer key
		// (pkToCk is sane)
		seen := map[string]bool{}
		e.Store.IteratePkToCk(func(_ ProviderPubKey, ck ConsumerPubKey) bool {
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
		e.Store.IteratePkToCk(func(pk ProviderPubKey, ck ConsumerPubKey) bool {
			if pkQueried, ok := e.Store.GetCkToPk(ck); ok {
				good = good && pkQueried.Equal(pk)
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
		e.Store.IterateCkToPk(func(ck ConsumerPubKey, _ ProviderPubKey) bool {
			found := false
			e.Store.IteratePkToCk(func(_, candidateCk ConsumerPubKey) bool {
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
		e.Store.IterateCkToPk(func(ck ConsumerPubKey, pk ProviderPubKey) bool {
			if m, ok := e.Store.GetCcaToLastUpdateMemo(ConsumerPubKeyToConsumerConsAddr(ck)); ok {
				if !pk.Equal(m.Pk) {
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
			cons := ConsumerPubKeyToConsumerConsAddr(*m.Ck)
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

	return good

}

type KeyMapStore struct {
	Store   sdk.KVStore
	ChainID ChainID
}

func (s *KeyMapStore) SetPkToCk(k ProviderPubKey, v ConsumerPubKey) {
	kbz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	vbz, err := v.Marshal()
	if err != nil {
		panic(err)
	}
	s.Store.Set(types.KeyMapPkToCkKey(s.ChainID, kbz), vbz)
}
func (s *KeyMapStore) SetCkToPk(k ConsumerPubKey, v ProviderPubKey) {
	kbz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	vbz, err := v.Marshal()
	if err != nil {
		panic(err)
	}
	s.Store.Set(types.KeyMapCkToPkKey(s.ChainID, kbz), vbz)
}
func (s *KeyMapStore) SetCcaToLastUpdateMemo(k ConsumerConsAddr, v ccvtypes.LastUpdateMemo) {
	kbz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	vbz, err := v.Marshal()
	if err != nil {
		panic(err)
	}
	s.Store.Set(types.KeyMapCkToMemoKey(s.ChainID, kbz), vbz)
}
func (s *KeyMapStore) GetPkToCk(k ProviderPubKey) (v ConsumerPubKey, found bool) {
	kbz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	if vbz := s.Store.Get(types.KeyMapPkToCkKey(s.ChainID, kbz)); vbz != nil {
		err := v.Unmarshal(vbz)
		if err != nil {
			panic(err)
		}
		return v, true
	}
	return v, false
}
func (s *KeyMapStore) GetCkToPk(k ConsumerPubKey) (v ProviderPubKey, found bool) {
	kbz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	if vbz := s.Store.Get(types.KeyMapCkToPkKey(s.ChainID, kbz)); vbz != nil {
		err := v.Unmarshal(vbz)
		if err != nil {
			panic(err)
		}
		return v, true
	}
	return v, false
}
func (s *KeyMapStore) GetCcaToLastUpdateMemo(k ConsumerConsAddr) (v ccvtypes.LastUpdateMemo, found bool) {
	kbz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	if vbz := s.Store.Get(types.KeyMapCkToMemoKey(s.ChainID, kbz)); vbz != nil {
		v := ccvtypes.LastUpdateMemo{}
		err := v.Unmarshal(vbz)
		if err != nil {
			panic(err)
		}
		return v, true
	}
	return v, false
}
func (s *KeyMapStore) DelPkToCk(k ProviderPubKey) {
	kbz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	s.Store.Delete(types.KeyMapPkToCkKey(s.ChainID, kbz))
}
func (s *KeyMapStore) DelCkToPk(k ConsumerPubKey) {
	kbz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	s.Store.Delete(types.KeyMapCkToPkKey(s.ChainID, kbz))
}
func (s *KeyMapStore) DelCcaToLastUpdateMemo(k ConsumerConsAddr) {
	kbz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	s.Store.Delete(types.KeyMapCkToMemoKey(s.ChainID, kbz))
}
func (s *KeyMapStore) IteratePkToCk(cb func(ProviderPubKey, ConsumerPubKey) bool) {
	prefix := types.KeyMapPkToCkChainPrefix(s.ChainID)
	iterator := sdk.KVStorePrefixIterator(s.Store, prefix)
	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		k := ProviderPubKey{}
		err := k.Unmarshal(iterator.Key()[len(prefix):])
		if err != nil {
			panic(err)
		}
		v := ConsumerPubKey{}
		err = v.Unmarshal(iterator.Value())
		if err != nil {
			panic(err)
		}
		if cb(k, v) {
			return
		}
	}
}
func (s *KeyMapStore) IterateCkToPk(cb func(ConsumerPubKey, ProviderPubKey) bool) {
	prefix := types.KeyMapCkToPkChainPrefix(s.ChainID)
	iterator := sdk.KVStorePrefixIterator(s.Store, prefix)
	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		k := ConsumerPubKey{}
		err := k.Unmarshal(iterator.Key()[len(prefix):])
		if err != nil {
			panic(err)
		}
		v := ProviderPubKey{}
		err = v.Unmarshal(iterator.Value())
		if err != nil {
			panic(err)
		}
		if cb(k, v) {
			return
		}
	}
}
func (s *KeyMapStore) IterateCcaToLastUpdateMemo(cb func(ConsumerConsAddr, ccvtypes.LastUpdateMemo) bool) {
	prefix := types.KeyMapCkToMemoChainPrefix(s.ChainID)
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

func (k Keeper) KeyMap(ctx sdk.Context, chainID string) *KeyMap {
	store := KeyMapStore{ctx.KVStore(k.storeKey), chainID}
	km := MakeKeyMap(&store)
	return &km
}
