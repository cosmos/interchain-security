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

- Whenever a consumer chain is added or removed a new Keymap instance needs to be created
with a store interface which handles all of its reading and writing.
	- Need to figure out exactly where/when to add/delete consumer chain instance
	- Need to figure out exactly where/when to add/remove validator instance (with default?)


*/

import (
	"errors"

	abci "github.com/tendermint/tendermint/abci/types"
	crypto "github.com/tendermint/tendermint/proto/tendermint/crypto"
)

type PK = crypto.PublicKey
type CK = crypto.PublicKey
type VSCID = uint64

type Memo struct {
	ck    CK
	pk    PK
	vscid VSCID
	power int64
}

type KeyMap struct {
	store    Store
	pkToCk   map[PK]CK
	ckToPk   map[CK]PK
	ckToMemo map[CK]Memo
}

type Store interface {
	GetPkToCk() map[PK]CK
	GetCkToPk() map[CK]PK
	GetCkToMemo() map[CK]Memo
	SetPkToCk(map[PK]CK)
	SetCkToPk(map[CK]PK)
	SetCkToMemo(map[CK]Memo)
}

func MakeKeyMap(store Store) KeyMap {
	return KeyMap{
		store: store,
	}
}

// GetAll reads all data from store
// The granularity of store access can be changed if needed for
// performance reasons.
func (e *KeyMap) GetAll() {
	e.pkToCk = e.store.GetPkToCk()
	e.ckToPk = e.store.GetCkToPk()
	e.ckToMemo = e.store.GetCkToMemo()
}

// SetAll write all data to store
// The granularity of store access can be changed if needed for
// performance reasons.
func (e *KeyMap) SetAll() {
	e.store.SetPkToCk(e.pkToCk)
	e.store.SetCkToPk(e.ckToPk)
	e.store.SetCkToMemo(e.ckToMemo)
}

// TODO:
func (e *KeyMap) SetProviderKeyToConsumerKey(pk PK, ck CK) error {
	e.GetAll()
	if _, ok := e.ckToPk[ck]; ok {
		return errors.New(`cannot reuse key which is in use or was recently in use`)
	}
	if _, ok := e.ckToMemo[ck]; ok {
		return errors.New(`cannot reuse key which is in use or was recently in use`)
	}
	if oldCk, ok := e.pkToCk[pk]; ok {
		delete(e.ckToPk, oldCk)
	}
	e.pkToCk[pk] = ck
	e.ckToPk[ck] = pk
	e.SetAll() // TODO: Try with defer
	return nil
}

// TODO: do regular query (CK for PK)

// TODO: use found instead of error
func (e *KeyMap) GetProviderKey(ck CK) (PK, error) {
	e.GetAll()
	if u, ok := e.ckToMemo[ck]; ok {
		return u.pk, nil
	} else if pk, ok := e.ckToPk[ck]; ok {
		return pk, nil
	} else {
		return crypto.PublicKey{}, errors.New("provider key not found for consumer key")
	}
}

// TODO:
func (e *KeyMap) PruneUnusedKeys(latestVscid VSCID) {
	e.GetAll()
	toDel := []CK{}
	for _, u := range e.ckToMemo {
		// If the last update was a deletion (0 power) and the update
		// matured then pruning is possible.
		if u.power == 0 && u.vscid <= latestVscid {
			toDel = append(toDel, u.ck)
		}
	}
	for _, ck := range toDel {
		delete(e.ckToMemo, ck)
	}
	e.SetAll()
}

// TODO:
func (e *KeyMap) ComputeUpdates(vscid VSCID, providerUpdates []abci.ValidatorUpdate) (consumerUpdates []abci.ValidatorUpdate) {

	e.GetAll()

	updates := map[PK]int64{}

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
func (e *KeyMap) inner(vscid VSCID, providerUpdates map[PK]int64) map[CK]int64 {

	pks := []PK{}

	// Grab provider keys where the assigned consumer key has changed
	for oldCk, u := range e.ckToMemo {
		if newCk, ok := e.pkToCk[u.pk]; ok {
			if oldCk != newCk && 0 < u.power {
				pks = append(pks, u.pk)
			}
		}
	}
	// Grab provider keys where the validator power has changed
	for pk := range providerUpdates {
		pks = append(pks, pk)
	}

	ret := map[CK]int64{}

	// Create a read only copy, so that we can query while writing
	// updates to the old version.
	ckToMemo_READ_ONLY := map[CK]Memo{}
	for ck, memo := range e.ckToMemo {
		ckToMemo_READ_ONLY[ck] = memo
	}

	for _, pk := range pks {
		for _, u := range ckToMemo_READ_ONLY {
			if u.pk == pk && 0 < u.power {
				// For each provider key for which there was already a positive update
				// create a deletion update for the associated consumer key.
				e.ckToMemo[u.ck] = Memo{ck: u.ck, pk: pk, vscid: vscid, power: 0}
				ret[u.ck] = 0
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
			if u.pk == pk && 0 < u.power {
				// There was previously a positive power update: copy it.
				power = u.power
			}
		}
		// There is a new validator power: use it.
		if newPower, ok := providerUpdates[pk]; ok {
			power = newPower
		}
		// Only ship update with positive powers. Zero power updates (deletions)
		// are handled in earlier block.
		if 0 < power {
			ck := e.pkToCk[pk]
			e.ckToMemo[ck] = Memo{ck: ck, pk: pk, vscid: vscid, power: power}
			ret[ck] = power
		}
	}

	return ret
}

// Returns true iff internal invariants hold
func (e *KeyMap) internalInvariants() bool {

	e.GetAll()

	// No two provider keys can map to the same consumer key
	// (pkToCk is sane)
	seen := map[CK]bool{}
	for _, ck := range e.pkToCk {
		if seen[ck] {
			return false
		}
		seen[ck] = true
	}

	// all values of pkToCk is a key of ckToPk
	// (reverse lookup is always possible)
	for _, ck := range e.pkToCk {
		if _, ok := e.ckToPk[ck]; !ok {
			return false
		}
	}

	// All consumer keys mapping to provider keys are actually
	// mapped to by the provider key.
	// (ckToPk is sane)
	for ck := range e.ckToPk {
		good := false
		for _, candidateCk := range e.pkToCk {
			if candidateCk == ck {
				good = true
				break
			}
		}
		if !good {
			return false
		}
	}

	// If a consumer key is mapped to a provider key (currently)
	// any memo containing the same consumer key has the same
	// mapping.
	// (Ensures lookups are correct)
	for ck, pk := range e.ckToPk {
		if u, ok := e.ckToMemo[ck]; ok {
			if pk != u.pk {
				return false
			}
		}
	}

	return true

}
