package keydel

import (
	"errors"
)

type PK = int
type CK = int
type VSCID = int

type update struct {
	key   int
	power int
}

type memo struct {
	ck    CK
	pk    PK
	vscid int
	power int
}

// TODO:
// 1. Integrate into kv store.
// 2. integrate into Provider::EndBlock,
// 3. integrate with create/destroy validator
// 4. TODO: document this file

type KeyDel struct {
	pkToCk   map[PK]CK
	CkToPk   map[CK]PK
	CkToMemo map[CK]memo
}

func MakeKeyDel() KeyDel {
	return KeyDel{
		pkToCk:   map[PK]CK{},
		CkToPk:   map[CK]PK{},
		CkToMemo: map[CK]memo{},
	}
}

// TODO:
func (e *KeyDel) SetProviderKeyToConsumerKey(lk PK, fk CK) error {
	inUse := false
	if _, ok := e.CkToPk[fk]; ok {
		inUse = true
	}
	if _, ok := e.CkToMemo[fk]; ok {
		inUse = true
	}
	if inUse {
		return errors.New(`cannot reuse key which is in use or was recently in use`)
	}
	if oldFk, ok := e.pkToCk[lk]; ok {
		delete(e.CkToPk, oldFk)
	}
	e.pkToCk[lk] = fk
	e.CkToPk[fk] = lk
	return nil
}

// TODO:
func (e *KeyDel) GetProviderKey(fk CK) (PK, error) {
	if u, ok := e.CkToMemo[fk]; ok {
		return u.pk, nil
	} else if lk, ok := e.CkToPk[fk]; ok {
		return lk, nil
	} else {
		return -1, errors.New("local key not found for foreign key")
	}
}

// TODO:
func (e *KeyDel) PruneUnusedKeys(latestVscid VSCID) {
	toDel := []CK{}
	for _, u := range e.CkToMemo {
		// If the last update was a deletion (0 power) and the update
		// matured then pruning is possible.
		if u.power == 0 && u.vscid <= latestVscid {
			toDel = append(toDel, u.ck)
		}
	}
	for _, fk := range toDel {
		delete(e.CkToMemo, fk)
	}
}

// TODO:
func (e *KeyDel) ComputeUpdates(vscid VSCID, providerUpdates []update) (consumerUpdates []update) {

	updates := map[PK]int{}

	for _, u := range providerUpdates {
		updates[u.key] = u.power
	}

	foreign := e.inner(vscid, updates)

	consumerUpdates = []update{}

	for fk, power := range foreign {
		consumerUpdates = append(consumerUpdates, update{key: fk, power: power})
	}

	return consumerUpdates
}

// do inner work as part of ComputeUpdates
func (e *KeyDel) inner(vscid VSCID, providerUpdates map[PK]int) map[CK]int {

	pks := []PK{}

	// Grab provider keys where the assigned consumer key has changed
	for oldCk, u := range e.CkToMemo {
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

	ret := map[CK]int{}

	// Create a read only copy, so that we can query while writing
	// updates to the old version.
	ckToMemo_READ_ONLY := map[CK]memo{}
	for ck, memo := range e.CkToMemo {
		ckToMemo_READ_ONLY[ck] = memo
	}

	for _, pk := range pks {
		for _, u := range ckToMemo_READ_ONLY {
			if u.pk == pk && 0 < u.power {
				// For each provider key for which there was already a positive update
				// create a deletion update for the associated consumer key.
				e.CkToMemo[u.ck] = memo{ck: u.ck, pk: pk, vscid: vscid, power: 0}
				ret[u.ck] = 0
			}
		}
	}

	for _, pk := range pks {
		// For each provider key where there was either
		// 1) already a positive power update
		// 2) the validator power has changed (and is still positive)
		// create a change update for the associated consumer key.

		power := 0
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
			e.CkToMemo[ck] = memo{ck: ck, pk: pk, vscid: vscid, power: power}
			ret[ck] = power
		}
	}

	return ret
}

// Returns true iff internal invariants hold
func (e *KeyDel) internalInvariants() bool {

	// No two local keys can map to the same foreign key
	// (lkToFk is sane)
	seen := map[CK]bool{}
	for _, fk := range e.pkToCk {
		if seen[fk] {
			return false
		}
		seen[fk] = true
	}

	// all values of lkToFk is a key of fkToLk
	// (reverse lookup is always possible)
	for _, fk := range e.pkToCk {
		if _, ok := e.CkToPk[fk]; !ok {
			return false
		}
	}

	// All foreign keys mapping to local keys are actually
	// mapped to by the local key.
	// (fkToLk is sane)
	for fk := range e.CkToPk {
		good := false
		for _, candidateFk := range e.pkToCk {
			if candidateFk == fk {
				good = true
				break
			}
		}
		if !good {
			return false
		}
	}

	// If a foreign key is mapped to a local key (currently)
	// any memo containing the same foreign key has the same
	// mapping.
	// (Ensures lookups are correct)
	for fk, lk := range e.CkToPk {
		if u, ok := e.CkToMemo[fk]; ok {
			if lk != u.pk {
				return false
			}
		}
	}

	return true

}
