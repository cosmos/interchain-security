package keymap

/*
TODO: I think roughly, what I need to do, to drive this thing to completion is

- [ ] more unit tests
- [ ] integration with SendValidatorUpdates
- [ ] integration with Consumer Initiated Slashing (receive request)
- [ ] integration with Consumer Initiated Slashing (send acks)
- [ ] integration with maturation (pruning)
- [ ] integration with Validator add / delete
- [ ] integration with RPC queries
- [ ] integration with msg server
- [ ] integration with pending changes
- [ ] include in diff test driver?
- [ ] include in any existing tests?
- [ ] maybe use sdk.prefix.Store?
- [ ] check the test excludes for coverage/static analysis ect. Need to make sure all tests are included!

- Whenever a consumer chain is added or removed a new Keymap instance needs to be created
with a store interface which handles all of its reading and writing.
	- Need to figure out exactly where/when to add/delete consumer chain instance
	- Need to figure out exactly where/when to add/remove validator instance (with default?)


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
type StringifiedConsumerConsAddr = string

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
	PkToCk   map[ProviderPubKey]ConsumerPubKey
	CkToPk   map[ConsumerPubKey]ProviderPubKey
	CkToMemo map[ConsumerPubKey]Memo
	CcaToCk  map[StringifiedConsumerConsAddr]ConsumerPubKey
}

type Store interface {
	GetPkToCk() map[ProviderPubKey]ConsumerPubKey
	GetCkToPk() map[ConsumerPubKey]ProviderPubKey
	GetCkToMemo() map[ConsumerPubKey]Memo
	GetCcaToCk() map[StringifiedConsumerConsAddr]ConsumerPubKey
	SetPkToCk(map[ProviderPubKey]ConsumerPubKey)
	SetCkToPk(map[ConsumerPubKey]ProviderPubKey)
	SetCkToMemo(map[ConsumerPubKey]Memo)
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
func (e *KeyMap) SetProviderKeyToConsumerKey(pk ProviderPubKey, ck ConsumerPubKey) error {
	e.GetAll()
	if _, ok := e.CkToPk[ck]; ok {
		return errors.New(`cannot reuse key which is in use or was recently in use`)
	}
	if _, ok := e.CkToMemo[ck]; ok {
		return errors.New(`cannot reuse key which is in use or was recently in use`)
	}
	if oldCk, ok := e.PkToCk[pk]; ok {
		delete(e.CkToPk, oldCk)
	}
	e.PkToCk[pk] = ck
	e.CkToPk[ck] = pk
	e.SetAll() // TODO: Try with defer
	return nil
}

// TODO: do regular query (CK for PK)

// TODO: use found instead of error
func (e *KeyMap) GetProviderPubKeyFromConsumerPubKey(ck ConsumerPubKey) (ProviderPubKey, error) {
	e.GetAll()
	if u, ok := e.CkToMemo[ck]; ok {
		return u.Pk, nil
	} else if pk, ok := e.CkToPk[ck]; ok {
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
		delete(e.CcaToCk, e.CkToMemo[ck].Cca)
		delete(e.CkToMemo, ck)
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
		if newCk, ok := e.PkToCk[u.Pk]; ok {
			if oldCk != newCk && 0 < u.Power {
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
	ckToMemo_READ_ONLY := map[ConsumerPubKey]Memo{}
	for ck, memo := range e.CkToMemo {
		ckToMemo_READ_ONLY[ck] = memo
	}

	for _, pk := range pks {
		for _, u := range ckToMemo_READ_ONLY {
			if u.Pk == pk && 0 < u.Power {
				// For each provider key for which there was already a positive update
				// create a deletion update for the associated consumer key.
				cca := consumerPubKeyToStringifiedConsumerConsAddr(u.Ck)
				e.CkToMemo[u.Ck] = Memo{Ck: u.Ck, Pk: pk, Vscid: vscid, Power: 0, Cca: cca}
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
			ck := e.PkToCk[pk]
			cca := consumerPubKeyToStringifiedConsumerConsAddr(ck)
			e.CkToMemo[ck] = Memo{Ck: ck, Pk: pk, Vscid: vscid, Power: power, Cca: cca}
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
			if _, ok := e.CkToPk[ck]; !ok {
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
				if candidateCk == ck {
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
			memo, found := e.CkToMemo[ck]
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
