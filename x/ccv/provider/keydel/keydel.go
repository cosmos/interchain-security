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
	foreignToGreatestVSCID map[FK]VSCID
}

func MakeKeyDel() KeyDel {
	return KeyDel{
		localToLastPositiveForeignUpdate: map[LK]update{},
		localToForeign:                   map[LK]FK{},
		foreignToLocal:                   map[FK]LK{},
		foreignToGreatestVSCID:           map[FK]VSCID{},
	}
}

func (e *KeyDel) SetLocalToForeign(lk LK, fk FK) {
	e.localToForeign[lk] = fk
}

func (e *KeyDel) GetLocal(fk FK) (LK, error) {
	if lk, ok := e.foreignToLocal[fk]; ok {
		return lk, nil
	} else {
		return -1, errors.New("Nope")
	}
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
	localToLastPositiveForeignUpdate := map[LK]update{}
	for lk, u := range e.localToLastPositiveForeignUpdate {
		localToLastPositiveForeignUpdate[lk] = u
	}

	// Iterate all local keys for which either the foreign key changed or there
	// has been a power update.
	for _, lk := range lks {
		if last, ok := e.localToLastPositiveForeignUpdate[lk]; ok {
			// If the key has previously been shipped in an update
			// delete it.
			foreignUpdates[last.key] = 0
			delete(localToLastPositiveForeignUpdate, lk)
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
			localToLastPositiveForeignUpdate[lk] = update{key: fk, power: power}
		}
	}

	e.localToLastPositiveForeignUpdate = localToLastPositiveForeignUpdate

	for fk := range foreignUpdates {
		e.foreignToGreatestVSCID[fk] = vscid
	}

	return foreignUpdates
}

func (e *KeyDel) ComputeUpdates(vscid VSCID, localUpdates []update) []update {

	local := map[LK]int{}

	for _, u := range localUpdates {
		local[u.key] = u.power
	}

	foreign := e.inner(vscid, local)

	ret := []update{}

	for fk, power := range foreign {
		ret = append(ret, update{key: fk, power: power})
	}

	return ret
}

func (e *KeyDel) Prune(mostRecentlyMaturedVscid VSCID) {
	toRemove := []FK{}
	for fk, vscid := range e.foreignToGreatestVSCID {
		if vscid <= mostRecentlyMaturedVscid {
			toRemove = append(toRemove, fk)
		}
	}
	for _, fk := range toRemove {
		delete(e.foreignToGreatestVSCID, fk)
		delete(e.foreignToLocal, fk)
	}
}
