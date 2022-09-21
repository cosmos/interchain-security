package keyguard

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

type KeyGuard struct {
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

func MakeKeyGuard() KeyGuard {
	return KeyGuard{
		localToLastPositiveForeignUpdate: map[LK]update{},
		localToForeign:                   map[LK]FK{},
		foreignToLocal:                   map[FK]LK{},
		foreignToGreatestVSCID:           map[FK]VSCID{},
	}
}

func (m *KeyGuard) SetLocalToForeign(lk LK, fk FK) {
	m.localToForeign[lk] = fk
}

func (m *KeyGuard) GetLocal(fk FK) (LK, error) {
	if lk, ok := m.foreignToLocal[fk]; ok {
		return lk, nil
	} else {
		return -1, errors.New("Nope")
	}
}

func (m *KeyGuard) inner(vscid VSCID, localUpdates map[LK]int) map[FK]int {

	lks := []LK{}

	// Key changes
	for lk, newFk := range m.localToForeign {
		if u, ok := m.localToLastPositiveForeignUpdate[lk]; ok {
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

	// need to go over every local key with a key change or a power update
	// add a deletion for all of these, that have a last positive update
	// need to go over every local key with a key change or a power update
	// 	if new power update is 0, do nothing
	//  if new power update is positive, use it
	//  else: use old power update, which must be positve

	// Iterate each lk for which the fk changed, or there is a power update
	for _, lk := range lks {
		power := 0
		// If a positive update was sent, undo it.
		// Store power for possible redo.
		if last, ok := m.localToLastPositiveForeignUpdate[lk]; ok {
			foreignUpdates[last.key] = 0
			power = last.power
			delete(m.localToLastPositiveForeignUpdate, lk)
		}
		// If there is a power update
		if newPower, ok := localUpdates[lk]; ok {
			power = newPower
		}
		// If power is 0, already deleted a few lines above
		// If power is positive, we are updating or redoing
		if 0 < power {
			fk := m.localToForeign[lk]
			foreignUpdates[fk] = power
			m.localToLastPositiveForeignUpdate[lk] = update{key: fk, power: power}
		}
	}

	for fk := range foreignUpdates {
		m.foreignToGreatestVSCID[fk] = vscid
	}

	return foreignUpdates
}

func (m *KeyGuard) ComputeUpdates(vscid VSCID, localUpdates []update) []update {

	local := map[LK]int{}

	for _, u := range localUpdates {
		local[u.key] = u.power
	}

	foreign := m.inner(vscid, local)

	ret := []update{}

	for fk, power := range foreign {
		ret = append(ret, update{key: fk, power: power})
	}

	return ret
}

func (m *KeyGuard) Prune(mostRecentlyMaturedVscid VSCID) {
	toRemove := []FK{}
	for fk, vscid := range m.foreignToGreatestVSCID {
		if vscid <= mostRecentlyMaturedVscid {
			toRemove = append(toRemove, fk)
		}
	}
	for _, fk := range toRemove {
		delete(m.foreignToGreatestVSCID, fk)
		delete(m.foreignToLocal, fk)
	}
}
