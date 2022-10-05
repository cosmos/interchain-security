package keydel

import (
	"errors"
)

type LK = int
type FK = int
type VSCID = int

type update struct {
	key   int
	power int
}

type memo struct {
	fk    FK
	lk    LK
	vscid int
	power int
}

// TODO:
// 1. Integrate into kv store.
// 2. integrate into Provider::EndBlock,
// 3. integrate with create/destroy validator

type KeyDel struct {
	lkToFk   map[LK]FK
	fkToLk   map[FK]LK
	fkToMemo map[FK]memo
}

func MakeKeyDel() KeyDel {
	return KeyDel{
		lkToFk:   map[LK]FK{},
		fkToLk:   map[FK]LK{},
		fkToMemo: map[FK]memo{},
	}
}

func (e *KeyDel) SetLocalToForeign(lk LK, fk FK) error {
	inUse := false
	if _, ok := e.fkToLk[fk]; ok {
		inUse = true
	}
	if _, ok := e.fkToMemo[fk]; ok {
		inUse = true
	}
	if inUse {
		return errors.New(`cannot reuse foreign key which is currently or recently in use`)
	}
	if oldFk, ok := e.lkToFk[lk]; ok {
		delete(e.fkToLk, oldFk)
	}
	e.lkToFk[lk] = fk
	e.fkToLk[fk] = lk
	return nil
}

func (e *KeyDel) GetLocal(fk FK) (LK, error) {
	if u, ok := e.fkToMemo[fk]; ok {
		return u.lk, nil
	} else if lk, ok := e.fkToLk[fk]; ok {
		return lk, nil
	} else {
		return -1, errors.New("local key not found for foreign key")
	}
}

func (e *KeyDel) Prune(vscid VSCID) {
	toDel := []FK{}
	for _, u := range e.fkToMemo {
		// If the last update was a deletion (0 power) and the update
		// matured then pruning is possible.
		if u.power == 0 && u.vscid <= vscid {
			toDel = append(toDel, u.fk)
		}
	}
	for _, fk := range toDel {
		delete(e.fkToMemo, fk)
	}
}

func (e *KeyDel) ComputeUpdates(vscid VSCID, localUpdates []update) (foreignUpdates []update) {

	local := map[LK]int{}

	for _, u := range localUpdates {
		local[u.key] = u.power
	}

	foreign := e.inner(vscid, local)

	foreignUpdates = []update{}

	for fk, power := range foreign {
		foreignUpdates = append(foreignUpdates, update{key: fk, power: power})
	}

	return foreignUpdates
}

func (e *KeyDel) inner(vscid VSCID, localUpdates map[LK]int) map[FK]int {

	lks := []LK{}

	// Grab lks for which fk changed
	for oldFk, u := range e.fkToMemo {
		if newFk, ok := e.lkToFk[u.lk]; ok {
			if oldFk != newFk && 0 < u.power {
				lks = append(lks, u.lk)
			}
		}
	}
	// Grab lks for which power changed
	for lk := range localUpdates {
		lks = append(lks, lk)
	}

	ret := map[FK]int{}

	fkToMemoClone := map[FK]memo{}
	for k, v := range e.fkToMemo {
		fkToMemoClone[k] = v
	}

	// Iterate all local keys for which there was previously a positive update.
	for _, lk := range lks {
		for _, u := range fkToMemoClone {
			if u.lk == lk && 0 < u.power {
				e.fkToMemo[u.fk] = memo{fk: u.fk, lk: lk, vscid: vscid, power: 0}
				ret[u.fk] = 0
			}
		}
	}

	// Iterate all local keys for which either the foreign key changed or there
	// has been a power update.
	for _, lk := range lks {
		power := 0
		for _, u := range fkToMemoClone {
			if u.lk == lk && 0 < u.power {
				power = u.power
			}
		}
		// If there is a new power use it.
		if newPower, ok := localUpdates[lk]; ok {
			power = newPower
		}
		// Only ship positive powers. Zero powers are accounted for above.
		if 0 < power {
			fk := e.lkToFk[lk]
			e.fkToMemo[fk] = memo{fk: fk, lk: lk, vscid: vscid, power: power}
			ret[fk] = power
		}
	}

	return ret
}

// Returns true iff internal invariants hold
func (e *KeyDel) internalInvariants() bool {

	// No two local keys can map to the same foreign key
	seen := map[FK]bool{}
	for _, fk := range e.lkToFk {
		if seen[fk] {
			return false
		}
		seen[fk] = true
	}

	// All foreign keys mapped to by local keys are noted
	for _, fk := range e.lkToFk {
		if _, ok := e.fkToLk[fk]; !ok {
			return false
		}
	}

	// All mapped to foreign keys are actually mapped to
	for fk := range e.fkToLk {
		good := false
		for _, candidateFk := range e.lkToFk {
			if candidateFk == fk {
				good = true
				break
			}
		}
		if !good {
			return false
		}
	}

	// If a foreign key is directly mapped to a local key
	// there is no disagreeing on the local key.
	for fk, lk := range e.fkToLk {
		if u, ok := e.fkToMemo[fk]; ok {
			if lk != u.lk {
				return false
			}
		}
	}

	return true

}
