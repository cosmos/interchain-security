package keydel

import "errors"

type LK = int
type FK = int
type VSCID = int

type update struct {
	key   FK
	power int
}

// TODO: I need to integrate this into the keyStore
// TODO: I need to integrate this into the system
// TODO: I need to integrate with staking Create/Destroy validator

type KeyDel struct {
	// A new key is added when a relevant update is returned by ComputeUpdates
	// the key is deleted at earliest after sending an update corresponding
	// to a call to staking::DeleteValidator TODO: impl this
	localToLastPositiveForeignUpdate map[LK]update
	// A new key is added on staking::CreateValidator
	// the key is deleted at earliest after sending an update corresponding
	// to a call to staking::DeleteValidator TODO: impl this
	localToForeign map[LK]FK
	// Prunable state
	foreignToLocal map[FK]LK
	// Prunable state
	foreignToGreatestVSCIDUsed map[FK]VSCID
}

func MakeKeyDel() KeyDel {
	return KeyDel{
		localToLastPositiveForeignUpdate: map[LK]update{},
		localToForeign:                   map[LK]FK{},
		foreignToLocal:                   map[FK]LK{},
		foreignToGreatestVSCIDUsed:       map[FK]VSCID{},
	}
}

func (e *KeyDel) SetLocalToForeign(lk LK, fk FK) error {
	if existingLk, ok := e.foreignToLocal[fk]; ok {
		if existingLk != lk {
			// We prevent reusing foreign keys which are still used for local
			// key lookups. Otherwise it would be possible for a local key A
			// to commit an infraction under the foreign key X and change
			// the mapping of foreign key X to a local key B before the evidence
			// arrives.
			return errors.New(`cannot reuse foreign key which is associated
			to a different local key`)
		}
	}
	e.localToForeign[lk] = fk
	return nil
}

func (e *KeyDel) GetLocal(fk FK) (LK, error) {
	if lk, ok := e.foreignToLocal[fk]; ok {
		return lk, nil
	} else {
		return -1, errors.New("Nope")
	}
}

func (e *KeyDel) Prune(mostRecentlyMaturedVscid VSCID) {
	toRemove := []FK{}
	for fk, vscid := range e.foreignToGreatestVSCIDUsed {
		if vscid <= mostRecentlyMaturedVscid {
			toRemove = append(toRemove, fk)
		}
	}
	for _, fk := range toRemove {
		delete(e.foreignToGreatestVSCIDUsed, fk)
		delete(e.foreignToLocal, fk)
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
			e.foreignToLocal[last.key] = lk
			e.foreignToGreatestVSCIDUsed[last.key] = vscid
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
			e.foreignToLocal[fk] = lk
			e.foreignToGreatestVSCIDUsed[fk] = vscid
		}
	}

	e.localToLastPositiveForeignUpdate = lkTLPFU

	return foreignUpdates
}

// Returns true iff internal invariants hold
func (e *KeyDel) internalInvariants() bool {
	// All keys of foreignToLocal and foreignToGreatestVSCIDUsed are equal
	for fk := range e.foreignToLocal {
		if _, ok := e.foreignToGreatestVSCIDUsed[fk]; !ok {
			return false
		}
	}
	for fk := range e.foreignToGreatestVSCIDUsed {
		if _, ok := e.foreignToLocal[fk]; !ok {
			return false
		}
	}
	seen := map[FK]bool{}
	// No two local keys can map to the same foreign key
	for _, fk := range e.localToForeign {
		if seen[fk] {
			return false
		}
		seen[fk] = true
	}
	return true
}
