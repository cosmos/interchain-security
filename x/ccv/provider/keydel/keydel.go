package keydel

import "errors"

type LK = int
type FK = int
type VSCID = int

type update struct {
	key   FK
	power int
}

// TODO:
// 1. Integrate into kv store.
// 2. integrate into Provider::EndBlock,
// 3. integrate with create/destroy validator

type KeyDel struct {
	// A new key is added on staking::CreateValidator
	// the key is deleted at earliest after sending an update corresponding
	// to a call to staking::DeleteValidator
	// At most one local key can map to a given foreign key
	localToForeign map[LK]FK
	// Is the foreign key mapped to in localToForeign?
	foreignIsMappedTo map[FK]bool
	// Prunable state
	usedForeignToLocal map[FK]LK
	// Prunable state
	usedForeignToLastVSCID map[FK]VSCID
	// A new key is added when a relevant update is returned by ComputeUpdates
	// the key is deleted at earliest after sending an update corresponding
	// to a call to staking::DeleteValidator
	localToLastPositiveForeignUpdate map[LK]update
}

func MakeKeyDel() KeyDel {
	return KeyDel{
		localToForeign:                   map[LK]FK{},
		foreignIsMappedTo:                map[FK]bool{},
		usedForeignToLocal:               map[FK]LK{},
		usedForeignToLastVSCID:           map[FK]VSCID{},
		localToLastPositiveForeignUpdate: map[LK]update{},
	}
}

func (e *KeyDel) SetLocalToForeign(lk LK, fk FK) error {
	if _, ok := e.foreignIsMappedTo[fk]; ok {
		return errors.New(`cannot reuse foreign key which is associated
			to a different local key`)
	}
	if _, ok := e.usedForeignToLocal[fk]; ok {
		// We prevent reusing foreign keys which are still used for local
		// key lookups. Otherwise it would be possible for a local key A
		// to commit an infraction under the foreign key X and change
		// the mapping of foreign key X to a local key B before evidence
		// arrives.
		return errors.New(`cannot reuse foreign key which was associated to a different
		local key and which is still queryable`)
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
	if lk, ok := e.usedForeignToLocal[fk]; ok {
		return lk, nil
	} else {
		return -1, errors.New("Nope")
	}
}

func (e *KeyDel) Prune(mostRecentlyMaturedVscid VSCID) {
	toRemove := []FK{}
	for fk, vscid := range e.usedForeignToLastVSCID {
		if vscid <= mostRecentlyMaturedVscid {
			toRemove = append(toRemove, fk)
		}
	}
	for _, fk := range toRemove {
		delete(e.usedForeignToLastVSCID, fk)
		delete(e.usedForeignToLocal, fk)
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

	// Iterate all local keys for which either the foreign key changed or there
	// has been a power update.
	for _, lk := range lks {
		if last, ok := e.localToLastPositiveForeignUpdate[lk]; ok {
			// If the key has previously been shipped in an update
			// delete it.
			foreignUpdates[last.key] = 0
			delete(lkTLPFU, lk)
			e.usedForeignToLocal[last.key] = lk
			e.usedForeignToLastVSCID[last.key] = vscid
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
		// Only ship positive powers.
		if 0 < power {
			fk := e.localToForeign[lk]
			foreignUpdates[fk] = power
			lkTLPFU[lk] = update{key: fk, power: power}
			e.usedForeignToLocal[fk] = lk
			e.usedForeignToLastVSCID[fk] = vscid
		}
	}

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

	// All local keys have a reverse lookup
	for _, fk := range e.localToForeign {
		if _, ok := e.usedForeignToLocal[fk]; !ok {
			return false
		}
	}

	return true

}
