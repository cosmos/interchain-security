package keydel

import "errors"

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

/*
TODO: there is a scenario which invalidates the current design of the system.

A vsc packet is sent whenever there is an unbonding op of any kind, or val power changes.
It is possible for a validator to be sent with positive power, and the maturity to be received.
This will delete the local key lookup, but it must be kept around.
*/

type KeyDel struct {
	// A new key is added on staking::CreateValidator
	// the key is deleted at earliest after sending an update corresponding
	// to a call to staking::DeleteValidator
	// At most one local key can map to a given foreign key
	localToForeign map[LK]FK
	// Is the foreign key mapped to in localToForeign?
	foreignIsMappedTo map[FK]bool
	//TODO:
	foreignToLastUpdate map[FK]lastUpdate
	// A new key is added when a relevant update is returned by ComputeUpdates
	// the key is deleted at earliest after sending an update corresponding
	// to a call to staking::DeleteValidator
	localToLastPositiveForeignUpdate map[LK]update
}

func MakeKeyDel() KeyDel {
	return KeyDel{
		localToForeign:                   map[LK]FK{},
		foreignIsMappedTo:                map[FK]bool{},
		foreignToLastUpdate:              map[FK]lastUpdate{},
		localToLastPositiveForeignUpdate: map[LK]update{},
	}
}

func (e *KeyDel) SetLocalToForeign(lk LK, fk FK) error {
	if _, ok := e.foreignIsMappedTo[fk]; ok {
		return errors.New(`cannot use foreign key which is 
						   already currently associated to a local key`)
	}
	if _, ok := e.foreignToLastUpdate[fk]; ok {
		// We prevent reusing foreign keys which are still used for local
		// key lookups. Otherwise it would be possible for a local key A
		// to commit an infraction under the foreign key X and change
		// the mapping of foreign key X to a local key B before evidence
		// arrives.
		return errors.New(`cannot reuse foreign key which was associated to
						   a different local key and which is still queryable`)
	}
	if otherFk, ok := e.localToForeign[lk]; ok {
		delete(e.foreignIsMappedTo, otherFk)
	}
	e.localToForeign[lk] = fk
	e.foreignIsMappedTo[fk] = true
	return nil
}

func (e *KeyDel) GetLocal(fk FK) (LK, error) {
	// TODO: make it possible lookup local keys even
	// when the foreign key has not yet been used?
	if u, ok := e.foreignToLastUpdate[fk]; ok {
		return u.lk, nil
	} else {
		return -1, errors.New("local key not found for foreign key")
	}
}

func (e *KeyDel) Prune(vscid VSCID) {
	toRemove := []FK{}
	for _, u := range e.foreignToLastUpdate {
		if u.vscid <= vscid && u.power == 0 {
			toRemove = append(toRemove, u.fk)
		}
	}
	for _, fk := range toRemove {
		delete(e.foreignToLastUpdate, fk)
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
	for lk, newFk := range e.localToForeign {
		if u, ok := e.localToLastPositiveForeignUpdate[lk]; ok {
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
	lkTLPFU := map[LK]update{}
	for lk, u := range e.localToLastPositiveForeignUpdate {
		lkTLPFU[lk] = u
	}

	// Iterate all local keys for which there was previously a positive update.
	for _, lk := range lks {
		if last, ok := e.localToLastPositiveForeignUpdate[lk]; ok {
			// Create a deletion update
			foreignUpdates[last.key] = 0
			delete(lkTLPFU, lk)
			e.foreignToLastUpdate[last.key] = lastUpdate{fk: last.key, lk: lk, vscid: vscid, power: 0}
		}
	}

	// Iterate all local keys for which either the foreign key changed or there
	// has been a power update.
	for _, lk := range lks {
		power := 0
		if last, ok := e.localToLastPositiveForeignUpdate[lk]; ok {
			// If there was a positive power before, use it.
			power = last.power
		}
		// If there is a new power use it.
		if newPower, ok := localUpdates[lk]; ok {
			power = newPower
		}
		// Only ship positive powers. Zero powers are accounted for above.
		if 0 < power {
			fk := e.localToForeign[lk]
			foreignUpdates[fk] = power
			lkTLPFU[lk] = update{key: fk, power: power}
			e.foreignToLastUpdate[fk] = lastUpdate{fk: fk, lk: lk, vscid: vscid, power: power}
		}
	}

	// TODO: I can replace RHS with some logic which does addition/deletion based on
	// power in e.usedForeignToLastUpdate??
	e.localToLastPositiveForeignUpdate = lkTLPFU

	return foreignUpdates
}

// Returns true iff internal invariants hold
func (e *KeyDel) internalInvariants() bool {

	// No two local keys can map to the same foreign key
	seen := map[FK]bool{}
	for _, fk := range e.localToForeign {
		if seen[fk] {
			return false
		}
		seen[fk] = true
	}

	// All foreign keys mapped to by local keys are noted
	for _, fk := range e.localToForeign {
		if _, ok := e.foreignIsMappedTo[fk]; !ok {
			return false
		}
	}

	// All mapped to foreign keys are actually mapped to
	for fk := range e.foreignIsMappedTo {
		good := false
		for _, mappedFK := range e.localToForeign {
			if mappedFK == fk {
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
