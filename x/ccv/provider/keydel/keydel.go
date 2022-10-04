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

type timedUpdate struct {
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
	lkToCurrFk map[LK]FK
	lkToLastFk map[LK]FK
	fkInUse    map[FK]bool
	fkToUpdate map[FK]timedUpdate
}

func MakeKeyDel() KeyDel {
	return KeyDel{
		lkToCurrFk: map[LK]FK{},
		lkToLastFk: map[LK]FK{},
		fkInUse:    map[FK]bool{},
		fkToUpdate: map[FK]timedUpdate{},
	}
}

func (e *KeyDel) SetLocalToForeign(lk LK, fk FK) error {

	inUse := false
	if _, ok := e.fkInUse[fk]; ok {
		inUse = true
	}
	if _, ok := e.fkToUpdate[fk]; ok {
		inUse = true
	}
	if inUse {
		return errors.New(`cannot reuse foreign key which is still in use for
						   local key lookups`)
	}
	if otherFk, ok := e.lkToCurrFk[lk]; ok {
		delete(e.fkInUse, otherFk)
	}
	e.lkToCurrFk[lk] = fk
	e.fkInUse[fk] = true
	return nil
}

func (e *KeyDel) GetLocal(fk FK) (LK, error) {
	// TODO: implement lookup for keys currently mapped
	// but that have not yet been used to compute an update
	if u, ok := e.fkToUpdate[fk]; ok {
		return u.lk, nil
	} else {
		return -1, errors.New("local key not found for foreign key")
	}
}

func (e *KeyDel) Prune(vscid VSCID) {
	toDel := []FK{}
	for _, u := range e.fkToUpdate {
		// If the last update was a deletion, and it has matured.
		if u.power == 0 && u.vscid <= vscid {
			toDel = append(toDel, u.fk)
		}
	}
	for _, fk := range toDel {
		delete(e.fkToUpdate, fk)
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

	// Grab all local keys for which the foreign key changed
	for lk, currFk := range e.lkToCurrFk {
		if lastFk, ok := e.lkToLastFk[lk]; ok {
			u := e.fkToUpdate[lastFk]
			if 0 < u.power && lastFk != currFk {
				// Has the key changed?
				lks = append(lks, lk)
			}
		}
	}
	// Grab all local keys for which there was a power update
	for lk := range localUpdates {
		lks = append(lks, lk)
	}

	ret := map[FK]int{}

	// Make a temporary copy
	lkToLastFkCopy := map[LK]FK{}
	for lk, fk := range e.lkToLastFk {
		lkToLastFkCopy[lk] = fk
	}

	// Iterate all local keys for which there was previously a positive update.
	for _, lk := range lks {
		if fk, ok := e.lkToLastFk[lk]; ok {
			if 0 < e.fkToUpdate[fk].power {
				// Create a deletion update
				ret[fk] = 0
				lkToLastFkCopy[lk] = fk
				e.fkToUpdate[fk] = timedUpdate{fk: fk, lk: lk, vscid: vscid, power: 0}
			}
		}
	}

	// Iterate all local keys for which either the foreign key changed or there
	// has been a power update.
	for _, lk := range lks {
		power := 0
		if fk, ok := e.lkToLastFk[lk]; ok {
			power = e.fkToUpdate[fk].power
		}
		// If there is a new power use it.
		if newPower, ok := localUpdates[lk]; ok {
			power = newPower
		}
		// Only ship positive powers. Zero powers are accounted for above.
		if 0 < power {
			fk := e.lkToCurrFk[lk]
			ret[fk] = power
			lkToLastFkCopy[lk] = fk
			e.fkToUpdate[fk] = timedUpdate{fk: fk, lk: lk, vscid: vscid, power: power}
		}
	}

	// TODO:???
	e.lkToLastFk = lkToLastFkCopy

	return ret
}

// Returns true iff internal invariants hold
func (e *KeyDel) internalInvariants() bool {

	// No two local keys can map to the same foreign key
	seen := map[FK]bool{}
	for _, fk := range e.lkToCurrFk {
		if seen[fk] {
			return false
		}
		seen[fk] = true
	}

	// All foreign keys mapped to by local keys are tracked
	for _, fk := range e.lkToCurrFk {
		if _, ok := e.fkInUse[fk]; !ok {
			return false
		}
	}
	// All tracked foreign keys are actually mapped to
	for fk := range e.fkInUse {
		good := false
		for _, candidateFk := range e.lkToCurrFk {
			if fk == candidateFk {
				// Mapped to by at least one lk
				good = true
				break
			}
		}
		if !good {
			return false
		}
	}

	return true

}
