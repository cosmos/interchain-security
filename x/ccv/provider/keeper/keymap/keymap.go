package keymap

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
I have tackled a lot of the above but the integration points still aren't well tested. The serialization/
deserialization approach is somewhat hacky but should have decent performance in practice. It has the benefit
of making the core logic much more testable.
There are some loose ends with the core logic w.r.t reverse queries. This happened when I realised the consensus
key was needed. This means the consensus key reverse map lookup doesn't have exactly the same semantics as the
other reverse lookup. There's a comment on this, but I should fix it and add a test.
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

import (
	"errors"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	abci "github.com/tendermint/tendermint/abci/types"
	crypto "github.com/tendermint/tendermint/proto/tendermint/crypto"
)

type ProviderPubKey = crypto.PublicKey
type ConsumerPubKey = crypto.PublicKey
type StringifiedProviderPubKey = string
type StringifiedConsumerPubKey = string
type StringifiedConsumerConsAddr = string

// TODO: document
// It's necessary to get a string deterministically for use
// in map lookups
func StringifyPubKey(k crypto.PublicKey) string {
	bytes, err := k.Marshal()
	if err != nil {
		panic(err)
	}
	return string(bytes)
}

// TODO:
func consumerPubKeyToStringifiedConsumerConsAddr(ck ConsumerPubKey) StringifiedConsumerConsAddr {
	sdkCk, err := cryptocodec.FromTmProtoPublicKey(ck)
	if err != nil {
		panic("could not get public key from tm proto public key for keymap lookup")
	}
	return string(sdk.GetConsAddress(sdkCk))
}

type VSCID = uint64

type Memo struct {
	Ck    ConsumerPubKey
	Pk    ProviderPubKey
	Cca   StringifiedConsumerConsAddr
	Vscid VSCID
	Power int64
}

type KeyMap struct {
	store    Store
	PkToCk   map[StringifiedProviderPubKey]ConsumerPubKey
	CkToPk   map[StringifiedConsumerPubKey]ProviderPubKey
	CkToMemo map[StringifiedConsumerPubKey]Memo
	// TODO: there's currently a slight asymmetry because
	// a consAddr is only lookupable if it is in ckToMemo
	// but ideally it should also be possible if the cpk
	// is a value in pkToCk
	CcaToCk map[StringifiedConsumerConsAddr]ConsumerPubKey
}

type Store interface {
	GetPkToCk() map[StringifiedProviderPubKey]ConsumerPubKey
	GetCkToPk() map[StringifiedConsumerPubKey]ProviderPubKey
	GetCkToMemo() map[StringifiedConsumerPubKey]Memo
	GetCcaToCk() map[StringifiedConsumerConsAddr]ConsumerPubKey
	SetPkToCk(map[StringifiedProviderPubKey]ConsumerPubKey)
	SetCkToPk(map[StringifiedConsumerPubKey]ProviderPubKey)
	SetCkToMemo(map[StringifiedConsumerPubKey]Memo)
	SetCcaToCk(map[StringifiedConsumerConsAddr]ConsumerPubKey)
}

func MakeKeyMap(store Store) KeyMap {
	return KeyMap{
		store: store,
	}
}

// GetAll reads all data from store
// The granularity of store access can be changed if needed for
// performance reasons. TODO: privatize
func (e *KeyMap) GetAll() {
	e.PkToCk = e.store.GetPkToCk()
	e.CkToPk = e.store.GetCkToPk()
	e.CkToMemo = e.store.GetCkToMemo()
	e.CcaToCk = e.store.GetCcaToCk()
}

// SetAll write all data to store
// The granularity of store access can be changed if needed for
// performance reasons. TODO: privatize
func (e *KeyMap) SetAll() {
	e.store.SetPkToCk(e.PkToCk)
	e.store.SetCkToPk(e.CkToPk)
	e.store.SetCkToMemo(e.CkToMemo)
	e.store.SetCcaToCk(e.CcaToCk)
}

// TODO:
func (e *KeyMap) SetProviderPubKeyToConsumerPubKey(pk ProviderPubKey, ck ConsumerPubKey) error {
	e.GetAll()
	if _, ok := e.CkToPk[StringifyPubKey(ck)]; ok {
		return errors.New(`cannot reuse key which is in use or was recently in use`)
	}
	if _, ok := e.CkToMemo[StringifyPubKey(ck)]; ok {
		return errors.New(`cannot reuse key which is in use or was recently in use`)
	}
	if oldCk, ok := e.PkToCk[StringifyPubKey(pk)]; ok {
		delete(e.CkToPk, StringifyPubKey(oldCk))
	}
	e.PkToCk[StringifyPubKey(pk)] = ck
	e.CkToPk[StringifyPubKey(ck)] = pk
	e.SetAll() // TODO: Try with defer
	return nil
}

func (e *KeyMap) GetCurrentConsumerPubKeyFromProviderPubKey(pk ProviderPubKey) (ck ConsumerPubKey, found bool) {
	e.GetAll()
	ck, found = e.PkToCk[StringifyPubKey(pk)]
	return ck, found
}

// TODO: use found instead of error
func (e *KeyMap) GetProviderPubKeyFromConsumerPubKey(ck ConsumerPubKey) (ProviderPubKey, error) {
	e.GetAll()
	if u, ok := e.CkToMemo[StringifyPubKey(ck)]; ok {
		return u.Pk, nil
	} else if pk, ok := e.CkToPk[StringifyPubKey(ck)]; ok {
		return pk, nil
	} else {
		return crypto.PublicKey{}, errors.New("provider key not found for consumer key")
	}
}

// TODO: use found instead of error
func (e *KeyMap) GetProviderPubKeyFromConsumerConsAddress(cca sdk.ConsAddress) (ProviderPubKey, error) {
	e.GetAll()
	ck := e.CcaToCk[string(cca)]
	return e.GetProviderPubKeyFromConsumerPubKey(ck)
}

// TODO:
func (e *KeyMap) PruneUnusedKeys(latestVscid VSCID) {
	e.GetAll()
	toDel := []ConsumerPubKey{}
	for _, u := range e.CkToMemo {
		// If the last update was a deletion (0 power) and the update
		// matured then pruning is possible.
		if u.Power == 0 && u.Vscid <= latestVscid {
			toDel = append(toDel, u.Ck)
		}
	}
	for _, ck := range toDel {
		delete(e.CcaToCk, e.CkToMemo[StringifyPubKey(ck)].Cca)
		delete(e.CkToMemo, StringifyPubKey(ck))
	}
	e.SetAll()
}

// TODO:
func (e *KeyMap) ComputeUpdates(vscid VSCID, providerUpdates []abci.ValidatorUpdate) (consumerUpdates []abci.ValidatorUpdate) {

	e.GetAll()

	updates := map[ProviderPubKey]int64{}

	for _, u := range providerUpdates {
		updates[u.PubKey] = u.Power
	}

	updates = e.inner(vscid, updates)

	consumerUpdates = []abci.ValidatorUpdate{}

	for ck, power := range updates {
		consumerUpdates = append(consumerUpdates, abci.ValidatorUpdate{PubKey: ck, Power: power})
	}

	e.SetAll()
	return consumerUpdates
}

// do inner work as part of ComputeUpdates
func (e *KeyMap) inner(vscid VSCID, providerUpdates map[ProviderPubKey]int64) map[ConsumerPubKey]int64 {

	pks := []ProviderPubKey{}

	// Grab provider keys where the assigned consumer key has changed
	for oldCk, u := range e.CkToMemo {
		if newCk, ok := e.PkToCk[StringifyPubKey(u.Pk)]; ok {
			if oldCk != StringifyPubKey(newCk) && 0 < u.Power {
				pks = append(pks, u.Pk)
			}
		}
	}
	// Grab provider keys where the validator power has changed
	for pk := range providerUpdates {
		pks = append(pks, pk)
	}

	ret := map[ConsumerPubKey]int64{}

	// Create a read only copy, so that we can query while writing
	// updates to the old version.
	ckToMemo_READ_ONLY := map[StringifiedConsumerPubKey]Memo{}
	for ck, memo := range e.CkToMemo {
		ckToMemo_READ_ONLY[ck] = memo
	}

	for _, pk := range pks {
		for _, u := range ckToMemo_READ_ONLY {
			if u.Pk == pk && 0 < u.Power {
				// For each provider key for which there was already a positive update
				// create a deletion update for the associated consumer key.
				cca := consumerPubKeyToStringifiedConsumerConsAddr(u.Ck)
				e.CkToMemo[StringifyPubKey(u.Ck)] = Memo{Ck: u.Ck, Pk: pk, Vscid: vscid, Power: 0, Cca: cca}
				e.CcaToCk[cca] = u.Ck
				ret[u.Ck] = 0
			}
		}
	}

	for _, pk := range pks {
		// For each provider key where there was either
		// 1) already a positive power update
		// 2) the validator power has changed (and is still positive)
		// create a change update for the associated consumer key.

		var power int64 = 0
		for _, u := range ckToMemo_READ_ONLY {
			if u.Pk == pk && 0 < u.Power {
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
			ck := e.PkToCk[StringifyPubKey(pk)]
			cca := consumerPubKeyToStringifiedConsumerConsAddr(ck)
			e.CkToMemo[StringifyPubKey(ck)] = Memo{Ck: ck, Pk: pk, Vscid: vscid, Power: power, Cca: cca}
			e.CcaToCk[cca] = ck
			ret[ck] = power
		}
	}

	return ret
}

// Returns true iff internal invariants hold
func (e *KeyMap) internalInvariants() bool {

	e.GetAll()

	{
		// No two provider keys can map to the same consumer key
		// (pkToCk is sane)
		seen := map[ConsumerPubKey]bool{}
		for _, ck := range e.PkToCk {
			if seen[ck] {
				return false
			}
			seen[ck] = true
		}
	}

	{
		// all values of pkToCk is a key of ckToPk
		// (reverse lookup is always possible)
		for _, ck := range e.PkToCk {
			if _, ok := e.CkToPk[StringifyPubKey(ck)]; !ok {
				return false
			}
		}
	}

	{
		// All consumer keys mapping to provider keys are actually
		// mapped to by the provider key.
		// (ckToPk is sane)
		for ck := range e.CkToPk {
			good := false
			for _, candidateCk := range e.PkToCk {
				if StringifyPubKey(candidateCk) == ck {
					good = true
					break
				}
			}
			if !good {
				return false
			}
		}
	}

	{
		// If a consumer key is mapped to a provider key (currently)
		// any memo containing the same consumer key has the same
		// mapping.
		// (Ensures lookups are correct)
		for ck, pk := range e.CkToPk {
			if u, ok := e.CkToMemo[ck]; ok {
				if pk != u.Pk {
					return false
				}
			}
		}
	}

	{
		// All entries in ckToMemo have a unique consumer consensus
		// address
		seen := map[StringifiedConsumerConsAddr]bool{}
		for _, memo := range e.CkToMemo {
			if _, found := seen[memo.Cca]; found {
				return false
			}
			seen[memo.Cca] = true
		}
	}

	{
		// All entries in ckToMemo have a consumer consensus
		// address which is a key in ccaToCk
		for _, memo := range e.CkToMemo {
			if _, found := e.CcaToCk[memo.Cca]; !found {
				return false
			}
		}
	}

	{
		// All entries in ccaToCk have a unique consumer pub key
		seen := map[ConsumerPubKey]bool{}
		for _, ck := range e.CcaToCk {
			if _, found := seen[ck]; found {
				return false
			}
			seen[ck] = true
		}
	}

	{
		// All entries in ccaToCk have a consumer pub key
		// which is a key of ckToMemo
		for cca, ck := range e.CcaToCk {
			memo, found := e.CkToMemo[StringifyPubKey(ck)]
			if !found {
				return false
			}
			if memo.Cca != cca {
				return false
			}
		}
	}

	return true

}
