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
	localToLastUpdate map[LK]update
	// A new key is added on staking::CreateValidator
	// the key is deleted at earliest after sending an update corresponding
	// to a call to staking::DeleteValidator TODO: impl this
	localToForeign map[LK]FK
	// Prunable state
	foreignToLocal map[FK]LK
	// Prunable state
	foreignToGreatestVSCID map[FK]VSCID
	// Ephemeral state: will be cleared after each call to ComputeUpdates
	localsWhichMustUpdate []LK
}

func MakeKeyGuard() KeyGuard {
	return KeyGuard{
		localToLastUpdate:      map[LK]update{},
		localToForeign:         map[LK]FK{},
		foreignToLocal:         map[FK]LK{},
		foreignToGreatestVSCID: map[FK]VSCID{},
		localsWhichMustUpdate:  []LK{},
	}
}

func (m *KeyGuard) SetLocalToForeign(lk LK, fk FK) {
	if currFk, ok := m.localToForeign[lk]; ok {
		if currFk == fk {
			return
		}
	}
	m.localToForeign[lk] = fk
	// If an update was created for lk
	if u, ok := m.localToLastUpdate[lk]; ok {
		// If that update was not a deletion
		if 0 < u.power {
			// We must create an update
			m.localsWhichMustUpdate = append(m.localsWhichMustUpdate, lk)
		}
	}
}

func (m *KeyGuard) GetLocal(fk FK) (LK, error) {
	if lk, ok := m.foreignToLocal[fk]; ok {
		return lk, nil
	} else {
		return -1, errors.New("Nope")
	}
}

func (m *KeyGuard) ComputeUpdates(vscid VSCID, localUpdates []update) (foreignUpdates []update) {

	foreignUpdates = []update{}

	// Create any updates for validators whose power did not change
	for _, lk := range m.localsWhichMustUpdate {
		currKey := m.localToForeign[lk]
		u := m.localToLastUpdate[lk]
		// Create an update which will delete the validator for the old key
		foreignUpdates = append(foreignUpdates, update{key: u.key, power: 0})
		// Create an update which will add the validator for the new key
		foreignUpdates = append(foreignUpdates, update{key: currKey, power: u.power})
	}
	m.localsWhichMustUpdate = []LK{}

	// Create any updates for validators whose powers did change
	for _, u := range localUpdates {
		// Check if the consumer has an old key
		if lastU, ok := m.localToLastUpdate[u.key]; ok {
			// Create an update which will delete the validator for the old key
			foreignUpdates = append(foreignUpdates, update{key: lastU.key, power: 0})
		}
		currKey := m.localToForeign[u.key]
		// Create an update which will add/update the validator for the current key
		foreignUpdates = append(foreignUpdates, update{key: currKey, power: u.power})
	}

	// Update internal bookkeeping
	for _, u := range foreignUpdates {
		m.foreignToGreatestVSCID[u.key] = vscid
		m.localToLastUpdate[m.foreignToLocal[u.key]] = u
	}

	return foreignUpdates
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
