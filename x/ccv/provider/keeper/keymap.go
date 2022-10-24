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
   - [ ] garbage collect pkToCk, ckToPk, ccaToCk if appropriate, when validator is destroyed

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
	SetCkToMemo(ConsumerPubKey, ccvtypes.Memo)
	SetCcaToCk(ConsumerConsAddr, ConsumerPubKey)
	GetPkToCk(ProviderPubKey) (ConsumerPubKey, bool)
	GetCkToPk(ConsumerPubKey) (ProviderPubKey, bool)
	GetCkToMemo(ConsumerPubKey) (ccvtypes.Memo, bool)
	GetCcaToCk(ConsumerConsAddr) (ConsumerPubKey, bool)
	DelPkToCk(ProviderPubKey)
	DelCkToPk(ConsumerPubKey)
	DelCkToMemo(ConsumerPubKey)
	DelCcaToCk(ConsumerConsAddr)
	IteratePkToCk(func(ProviderPubKey, ConsumerPubKey) bool)
	IterateCkToPk(func(ConsumerPubKey, ProviderPubKey) bool)
	IterateCkToMemo(func(ConsumerPubKey, ccvtypes.Memo) bool)
	IterateCcaToCk(func(ConsumerConsAddr, ConsumerPubKey) bool)
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
	// TODO: comment
	if _, ok := e.Store.GetCkToPk(ck); ok {
		return errors.New(`cannot reuse key which is in use or was recently in use`)
	}
	// TODO: comment
	if _, ok := e.Store.GetCkToMemo(ck); ok {
		return errors.New(`cannot reuse key which is in use or was recently in use`)
	}
	if oldCk, ok := e.Store.GetPkToCk(pk); ok {
		e.Store.DelCkToPk(oldCk)
	}
	e.Store.SetPkToCk(pk, ck)
	e.Store.SetCkToPk(ck, pk)
	// TODO: check leak
	e.Store.SetCcaToCk(ConsumerPubKeyToConsumerConsAddr(ck), ck)
	return nil
}

func (e *KeyMap) GetCurrentConsumerPubKeyFromProviderPubKey(pk ProviderPubKey) (ck ConsumerPubKey, found bool) {
	return e.Store.GetPkToCk(pk)
}

func (e *KeyMap) GetProviderPubKeyFromConsumerPubKey(ck ConsumerPubKey) (pk ProviderPubKey, found bool) {
	if u, found := e.Store.GetCkToMemo(ck); found {
		return *u.Pk, true
	}
	return e.Store.GetCkToPk(ck)
}

func (e *KeyMap) GetProviderPubKeyFromConsumerConsAddress(cca sdk.ConsAddress) (pk ProviderPubKey, found bool) {
	if ck, found := e.Store.GetCcaToCk(cca); found {
		return e.GetProviderPubKeyFromConsumerPubKey(ck)
	}
	return pk, false
}

func (e *KeyMap) PruneUnusedKeys(latestVscid VSCID) {

	toDel := []ConsumerPubKey{}
	e.Store.IterateCkToMemo(func(cpk ConsumerPubKey, m ccvtypes.Memo) bool {
		if m.Power == 0 && m.Vscid <= latestVscid {
			toDel = append(toDel, *m.Ck)
		}
		return false
	})
	for _, ck := range toDel {
		m, found := e.Store.GetCkToMemo(ck)
		if !found {
			panic("must find memo for consumer key ck")
		}
		e.Store.DelCkToMemo(ck)
		if _, found := e.Store.GetCkToPk(ck); !found {
			e.Store.DelCcaToCk(m.Cca)
		}
	}
}

func (e *KeyMap) ComputeUpdates(vscid VSCID, providerUpdates []abci.ValidatorUpdate) (consumerUpdates []abci.ValidatorUpdate) {

	updates := map[ProviderPubKey]int64{}

	for _, u := range providerUpdates {
		updates[u.PubKey] = u.Power
	}

	updates = e.inner(vscid, updates)

	consumerUpdates = []abci.ValidatorUpdate{}

	for ck, power := range updates {
		consumerUpdates = append(consumerUpdates, abci.ValidatorUpdate{PubKey: ck, Power: power})
	}

	return consumerUpdates
}

// do inner work as part of ComputeUpdates
func (e *KeyMap) inner(vscid VSCID, providerUpdates map[ProviderPubKey]int64) map[ConsumerPubKey]int64 {

	seen := map[string]bool{}
	pks := []ProviderPubKey{}

	// Grab provider keys where the assigned consumer key has changed
	e.Store.IterateCkToMemo(func(oldCk ConsumerPubKey, m ccvtypes.Memo) bool {
		if newCk, ok := e.Store.GetPkToCk(*m.Pk); ok {
			str := DeterministicStringify(*m.Pk)
			// TODO: is !seen[str] needed?
			if !seen[str] && !oldCk.Equal(newCk) && 0 < m.Power { // TODO: comment why 0 < needed
				pks = append(pks, *m.Pk)
				seen[str] = true
			}
		}
		return false
	})

	// Grab provider keys where the validator power has changed
	for pk := range providerUpdates {
		str := DeterministicStringify(pk)
		if !seen[str] {
			pks = append(pks, pk)
		}
	}

	canonicalKey := map[string]ConsumerPubKey{}
	ret := map[ConsumerPubKey]int64{}

	// Create a read only copy, so that we can query while writing
	// updates to the old version.
	ckToMemo_READ_ONLY := map[ConsumerPubKey]ccvtypes.Memo{}
	e.Store.IterateCkToMemo(func(ck ConsumerPubKey, m ccvtypes.Memo) bool {
		// TODO: use determinsitic map key
		ckToMemo_READ_ONLY[ck] = m
		return false
	})

	// TODO: add comment what is this block for?

	for i := range pks {
		pk := pks[i]
		for _, u := range ckToMemo_READ_ONLY {
			if u.Pk.Equal(pk) && 0 < u.Power {
				// For each provider key for which there was already a positive update
				// create a deletion update for the associated consumer key.
				cca := ConsumerPubKeyToConsumerConsAddr(*u.Ck)
				e.Store.SetCkToMemo(*u.Ck, ccvtypes.Memo{Ck: u.Ck, Pk: &pk, Vscid: vscid, Power: 0, Cca: cca})
				e.Store.SetCcaToCk(cca, *u.Ck)
				ret[*u.Ck] = 0
				canonicalKey[DeterministicStringify(*u.Ck)] = *u.Ck
			}
		}
	}

	// TODO: add comment what is this block for?

	for i := range pks {
		pk := pks[i]
		// For each provider key where there was either
		// 1) already a positive power update
		// 2) the validator power has changed (and is positive)
		// create a change update for the associated consumer key.

		var power int64 = 0
		for _, u := range ckToMemo_READ_ONLY {
			if u.Pk.Equal(pk) && 0 < u.Power {
				// There was previously a positive power update: copy it.
				power = u.Power
			}
		}
		// There is a new validator power: use it.
		if newPower, ok := providerUpdates[pk]; ok {
			power = newPower
		}
		// Only ship update with positive powers. Zero power updates (deletions)
		// are handled in earlier block.
		if 0 < power {
			ck, found := e.Store.GetPkToCk(pk)
			if !found {
				panic("must find ck for pk")
			}
			cca := ConsumerPubKeyToConsumerConsAddr(ck)
			e.Store.SetCkToMemo(ck, ccvtypes.Memo{Ck: &ck, Pk: &pk, Vscid: vscid, Power: power, Cca: cca})
			e.Store.SetCcaToCk(cca, ck)
			if k, found := canonicalKey[DeterministicStringify(ck)]; found {
				ret[k] = power
			} else {
				ret[ck] = power
			}
		}
	}

	return ret
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
		// All values of pkToCk is a key of ccaToCk
		// (reverse lookup is always possible, using consAddr)
		e.Store.IteratePkToCk(func(pk ProviderPubKey, ck ConsumerPubKey) bool {
			cca := ConsumerPubKeyToConsumerConsAddr(ck)
			ckQueried, found := e.Store.GetCcaToCk(cca)
			good = good && found

			if pkQueried, ok := e.Store.GetCkToPk(ckQueried); ok {
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
			if m, ok := e.Store.GetCkToMemo(ck); ok {
				if !pk.Equal(m.Pk) {
					good = false
				}
			}
			return false
		})
	}

	{
		// All entries in ckToMemo have a unique consumer consensus
		// address
		seen := map[string]bool{}
		e.Store.IterateCkToMemo(func(_ ConsumerPubKey, m ccvtypes.Memo) bool {
			if _, found := seen[string(m.Cca)]; found {
				good = false
			}
			seen[string(m.Cca)] = true
			return false
		})

	}

	{
		// All entries in ckToMemo have a consumer consensus
		// address which is a key in ccaToCk
		e.Store.IterateCkToMemo(func(_ ConsumerPubKey, m ccvtypes.Memo) bool {
			if _, found := e.Store.GetCcaToCk(m.Cca); !found {
				good = false
			}
			return false
		})
	}

	{
		// All entries in ccaToCk have a unique consumer pub key
		seen := map[string]bool{}
		e.Store.IterateCcaToCk(func(_ ConsumerConsAddr, ck ConsumerPubKey) bool {
			if _, found := seen[DeterministicStringify(ck)]; found {
				good = false
			}
			seen[DeterministicStringify(ck)] = true
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
func (s *KeyMapStore) SetCkToMemo(k ConsumerPubKey, v ccvtypes.Memo) {
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
func (s *KeyMapStore) SetCcaToCk(k ConsumerConsAddr, v ConsumerPubKey) {
	kbz := []byte(k)
	vbz, err := v.Marshal()
	if err != nil {
		panic(err)
	}
	s.Store.Set(types.KeyMapCcaToCkKey(s.ChainID, kbz), vbz)
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
func (s *KeyMapStore) GetCkToMemo(k ConsumerPubKey) (v ccvtypes.Memo, found bool) {
	kbz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	if vbz := s.Store.Get(types.KeyMapCkToMemoKey(s.ChainID, kbz)); vbz != nil {
		v := ccvtypes.Memo{}
		err := v.Unmarshal(vbz)
		if err != nil {
			panic(err)
		}
		return v, true
	}
	return v, false
}
func (s *KeyMapStore) GetCcaToCk(k ConsumerConsAddr) (v ConsumerPubKey, found bool) {
	kbz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	if vbz := s.Store.Get(types.KeyMapCcaToCkKey(s.ChainID, kbz)); vbz != nil {
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
func (s *KeyMapStore) DelCkToMemo(k ConsumerPubKey) {
	kbz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	s.Store.Delete(types.KeyMapCkToMemoKey(s.ChainID, kbz))
}
func (s *KeyMapStore) DelCcaToCk(k ConsumerConsAddr) {
	kbz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	s.Store.Delete(types.KeyMapCcaToCkKey(s.ChainID, kbz))
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
func (s *KeyMapStore) IterateCkToMemo(cb func(ConsumerPubKey, ccvtypes.Memo) bool) {
	prefix := types.KeyMapCkToMemoChainPrefix(s.ChainID)
	iterator := sdk.KVStorePrefixIterator(s.Store, prefix)
	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		k := ConsumerPubKey{}
		err := k.Unmarshal(iterator.Key()[len(prefix):])
		if err != nil {
			panic(err)
		}
		v := ccvtypes.Memo{}
		err = v.Unmarshal(iterator.Value())
		if err != nil {
			panic(err)
		}
		if cb(k, v) {
			return
		}
	}
}
func (s *KeyMapStore) IterateCcaToCk(cb func(ConsumerConsAddr, ConsumerPubKey) bool) {
	prefix := types.KeyMapCcaToCkChainPrefix(s.ChainID)
	iterator := sdk.KVStorePrefixIterator(s.Store, prefix)
	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		k := sdk.ConsAddress(iterator.Key()[len(prefix):])
		v := ConsumerPubKey{}
		err := v.Unmarshal(iterator.Value())
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
