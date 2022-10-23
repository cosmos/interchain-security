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
   	- [ ] consumer genesis
   		For this I think it is sufficient to map through any defaults, just as in SendValidatorUpdates
   		and call ComputeUpdates with a 0 vscid. This should allow future pruning.
   	- [ ] provider genesis / init from genesis
   	- [ ] consumer removal

   In terms of testing, the current status is

   x/ccv/provider/keeper/keymap :: go test ./...          | passes
   x/ccv/provider/keeper/       :: go test keymap_test.go | passes
   make test-diff                                         | fails
   	I think diff tests should be easy to make work with default mappings once I implement proper consumer genesis
   	I will also have to manually LoadKeyMaps somewhere in the driver setup
   	It would be a great extension to add random live mappings to diff tests
   make test-short										   | fails
   	At least FAIL: TestHandleSlashPacketDoubleSigning happens. This is to be expected
   	because some kind of reverse mapping knowledge needs to be added to the test

   I didn't check the other tests yet



*/

// TODO: for each of the logic method which would have change the content of one of the old maps,
// e.g. when SetAll was called
// I need to delete each old value and replace/add each new value

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
	SetPkToCkValue(ProviderPubKey, ConsumerPubKey)
	SetCkToPkValue(ConsumerPubKey, ProviderPubKey)
	SetCkToMemoValue(ConsumerPubKey, ccvtypes.Memo)
	SetCcaToCkValue(ConsumerConsAddr, ConsumerPubKey)
	GetPkToCkValue(ProviderPubKey) (ConsumerPubKey, bool)
	GetCkToPkValue(ConsumerPubKey) (ProviderPubKey, bool)
	GetCkToMemoValue(ConsumerPubKey) (ccvtypes.Memo, bool)
	GetCcaToCkValue(ConsumerConsAddr) (ConsumerPubKey, bool)
	DelPkToCkKey(ProviderPubKey)
	DelCkToPkKey(ConsumerPubKey)
	DelCkToMemoKey(ConsumerPubKey)
	DelCcaToCkKey(ConsumerConsAddr)
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
	if _, ok := e.Store.GetCkToPkValue(ck); ok {
		return errors.New(`cannot reuse key which is in use or was recently in use`)
	}
	if _, ok := e.Store.GetCkToMemoValue(ck); ok {
		return errors.New(`cannot reuse key which is in use or was recently in use`)
	}
	if oldCk, ok := e.Store.GetPkToCkValue(pk); ok {
		e.Store.DelCkToPkKey(oldCk)
	}
	e.Store.SetPkToCkValue(pk, ck)
	e.Store.SetCkToPkValue(ck, pk)
	e.Store.SetCcaToCkValue(ConsumerPubKeyToConsumerConsAddr(ck), ck)
	return nil
}

func (e *KeyMap) GetCurrentConsumerPubKeyFromProviderPubKey(pk ProviderPubKey) (ck ConsumerPubKey, found bool) {
	return e.Store.GetPkToCkValue(pk)
}

func (e *KeyMap) GetProviderPubKeyFromConsumerPubKey(ck ConsumerPubKey) (pk ProviderPubKey, found bool) {
	if u, found := e.Store.GetCkToMemoValue(ck); found {
		return *u.Pk, true
	}
	return e.Store.GetCkToPkValue(ck)
}

func (e *KeyMap) GetProviderPubKeyFromConsumerConsAddress(cca sdk.ConsAddress) (pk ProviderPubKey, found bool) {
	if ck, found := e.Store.GetCcaToCkValue(cca); found {
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
		m, found := e.Store.GetCkToMemoValue(ck)
		if !found {
			panic("must find memo for consumer key ck")
		}
		e.Store.DelCkToMemoKey(ck)
		if _, found := e.Store.GetCkToPkValue(ck); !found {
			e.Store.DelCcaToCkKey(m.Cca)
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
		if newCk, ok := e.Store.GetPkToCkValue(*m.Pk); ok {
			str := DeterministicStringify(*m.Pk)
			if !seen[str] && !oldCk.Equal(newCk) && 0 < m.Power {
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
		ckToMemo_READ_ONLY[ck] = m
		return false
	})

	for i := range pks {
		pk := pks[i]
		for _, u := range ckToMemo_READ_ONLY {
			if u.Pk.Equal(pk) && 0 < u.Power {
				// For each provider key for which there was already a positive update
				// create a deletion update for the associated consumer key.
				cca := ConsumerPubKeyToConsumerConsAddr(*u.Ck)
				e.Store.SetCkToMemoValue(*u.Ck, ccvtypes.Memo{Ck: u.Ck, Pk: &pk, Vscid: vscid, Power: 0, Cca: cca})
				e.Store.SetCcaToCkValue(cca, *u.Ck)
				ret[*u.Ck] = 0
				canonicalKey[DeterministicStringify(*u.Ck)] = *u.Ck
			}
		}
	}

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
			ck, found := e.Store.GetPkToCkValue(pk)
			if !found {
				panic("must find ck for pk")
			}
			cca := ConsumerPubKeyToConsumerConsAddr(ck)
			e.Store.SetCkToMemoValue(ck, ccvtypes.Memo{Ck: &ck, Pk: &pk, Vscid: vscid, Power: power, Cca: cca})
			e.Store.SetCcaToCkValue(cca, ck)
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
			if pkQueried, ok := e.Store.GetCkToPkValue(ck); ok {
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
			ckQueried, found := e.Store.GetCcaToCkValue(cca)
			good = good && found

			if pkQueried, ok := e.Store.GetCkToPkValue(ckQueried); ok {
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
			if m, ok := e.Store.GetCkToMemoValue(ck); ok {
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
			if _, found := e.Store.GetCcaToCkValue(m.Cca); !found {
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

func (s *KeyMapStore) SetPkToCkValue(k ProviderPubKey, v ConsumerPubKey) {
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
func (s *KeyMapStore) SetCkToPkValue(k ConsumerPubKey, v ProviderPubKey) {
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
func (s *KeyMapStore) SetCkToMemoValue(k ConsumerPubKey, v ccvtypes.Memo) {
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
func (s *KeyMapStore) SetCcaToCkValue(k ConsumerConsAddr, v ConsumerPubKey) {
	kbz := []byte(k)
	vbz, err := v.Marshal()
	if err != nil {
		panic(err)
	}
	s.Store.Set(types.KeyMapCcaToCkKey(s.ChainID, kbz), vbz)
}
func (s *KeyMapStore) GetPkToCkValue(k ProviderPubKey) (v ConsumerPubKey, found bool) {
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
func (s *KeyMapStore) GetCkToPkValue(k ConsumerPubKey) (v ProviderPubKey, found bool) {
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
func (s *KeyMapStore) GetCkToMemoValue(k ConsumerPubKey) (v ccvtypes.Memo, found bool) {
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
func (s *KeyMapStore) GetCcaToCkValue(k ConsumerConsAddr) (v ConsumerPubKey, found bool) {
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

func (s *KeyMapStore) DelPkToCkKey(k ProviderPubKey) {
	kbz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	s.Store.Delete(types.KeyMapPkToCkKey(s.ChainID, kbz))
}
func (s *KeyMapStore) DelCkToPkKey(k ConsumerPubKey) {
	kbz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	s.Store.Delete(types.KeyMapCkToPkKey(s.ChainID, kbz))
}
func (s *KeyMapStore) DelCkToMemoKey(k ConsumerPubKey) {
	kbz, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	s.Store.Delete(types.KeyMapCkToMemoKey(s.ChainID, kbz))
}
func (s *KeyMapStore) DelCcaToCkKey(k ConsumerConsAddr) {
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
