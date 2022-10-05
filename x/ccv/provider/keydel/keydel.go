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

type lastUpdate struct {
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
	lkToFk             map[LK]FK
	fkInUse            map[FK]bool
	fkToUpdate         map[FK]lastUpdate
	lkToPositiveUpdate map[LK]update
}

func MakeKeyDel() KeyDel {
	return KeyDel{
		lkToFk:             map[LK]FK{},
		fkInUse:            map[FK]bool{},
		fkToUpdate:         map[FK]lastUpdate{},
		lkToPositiveUpdate: map[LK]update{},
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
		return errors.New(`cannot reuse foreign key which is currently being used for lookups`)
	}
	if oldFk, ok := e.lkToFk[lk]; ok {
		delete(e.fkInUse, oldFk)
	}
	e.lkToFk[lk] = fk
	e.fkInUse[fk] = true
	return nil
}

func (e *KeyDel) GetLocal(fk FK) (LK, error) {
	// TODO: implement lookups via keys current key
	if u, ok := e.fkToUpdate[fk]; ok {
		return u.lk, nil
	} else {
		return -1, errors.New("local key not found for foreign key")
	}
}

func (e *KeyDel) Prune(vscid VSCID) {
	toDel := []FK{}
	for _, u := range e.fkToUpdate {
		// If the last update was a deletion (0 power) and the update
		// matured then pruning is possible.
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

	// Key changes
	for lk, newFk := range e.lkToFk {
		if u, ok := e.lkToPositiveUpdate[lk]; ok {
			oldFk := u.key
			if oldFk != newFk {
				lks = append(lks, lk)
			}
		}
	}
	// Power changes
	for lk := range localUpdates {
		lks = append(lks, lk)
	}

	foreignUpdates := map[FK]int{}

	// Make a temporary copy
	lkToPU := map[LK]update{}
	for lk, u := range e.lkToPositiveUpdate {
		lkToPU[lk] = u
	}

	// Iterate all local keys for which there was previously a positive update.
	for _, lk := range lks {
		if last, ok := e.lkToPositiveUpdate[lk]; ok {
			// Create a deletion update
			foreignUpdates[last.key] = 0
			delete(lkToPU, lk)
			e.fkToUpdate[last.key] = lastUpdate{fk: last.key, lk: lk, vscid: vscid, power: 0}
		}
	}

	// Iterate all local keys for which either the foreign key changed or there
	// has been a power update.
	for _, lk := range lks {
		power := 0
		if last, ok := e.lkToPositiveUpdate[lk]; ok {
			// If there was a positive power before, use it.
			power = last.power
		}
		// If there is a new power use it.
		if newPower, ok := localUpdates[lk]; ok {
			power = newPower
		}
		// Only ship positive powers. Zero powers are accounted for above.
		if 0 < power {
			fk := e.lkToFk[lk]
			foreignUpdates[fk] = power
			lkToPU[lk] = update{key: fk, power: power}
			e.fkToUpdate[fk] = lastUpdate{fk: fk, lk: lk, vscid: vscid, power: power}
		}
	}

	e.lkToPositiveUpdate = lkToPU

	return foreignUpdates
}

// Returns true iff internal invariants hold
func (e *KeyDel) internalInvariants() bool {

	// If an update is stored in positive update, the last update
	// for the foreign key was not 0
	for _, u := range e.lkToPositiveUpdate {
		if e.fkToUpdate[u.key].power == 0 {
			return false
		}
	}

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
		if _, ok := e.fkInUse[fk]; !ok {
			return false
		}
	}

	// All mapped to foreign keys are actually mapped to
	for fk := range e.fkInUse {
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

	return true

}
