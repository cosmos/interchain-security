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
	// Ephemeral state: will be cleared after each call to ComputeUpdates
	localsWhichMustUpdate []LK
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
		localsWhichMustUpdate:            []LK{},
	}
}

func (m *KeyGuard) SetLocalToForeign(lk LK, fk FK) {
	m.localToForeign[lk] = fk
	if _, ok := m.localToLastPositiveForeignUpdate[lk]; ok {
		// We must create an update
		m.localsWhichMustUpdate = append(m.localsWhichMustUpdate, lk)
	}
}

func (m *KeyGuard) GetLocal(fk FK) (LK, error) {
	if lk, ok := m.foreignToLocal[fk]; ok {
		return lk, nil
	} else {
		return -1, errors.New("Nope")
	}
}

func (m *KeyGuard) ComputeUpdates(vscid VSCID, localUpdates []update) []update {

	foreignUpdates := map[FK]int{}

	// Create updates for any locals whose foreign key changed
	// NOTE: this includes the case of updating to the same foreign key
	for _, lk := range m.localsWhichMustUpdate {
		fk := m.localToForeign[lk]
		fu := m.localToLastPositiveForeignUpdate[lk]
		// Create an update which will delete the validator for the old key
		foreignUpdates[fu.key] = 0
		delete(m.localToLastPositiveForeignUpdate, lk)
		// Create an update which will add the validator for the new key
		foreignUpdates[fk] = fu.power
		m.localToLastPositiveForeignUpdate[lk] = update{key: fk, power: fu.power}
	}

	m.localsWhichMustUpdate = []LK{}

	for _, localUpdate := range localUpdates {
		if fu, ok := m.localToLastPositiveForeignUpdate[localUpdate.key]; ok {
			// If an update for the local key existed, send a deletion
			foreignUpdates[fu.key] = 0
		}
		fk := m.localToForeign[localUpdate.key]
		// Create an update which will add or update the validator for the current key
		foreignUpdates[fk] = localUpdate.power
		if 0 < localUpdate.power {
			m.localToLastPositiveForeignUpdate[localUpdate.key] = update{key: fk, power: localUpdate.power}
		} else {
			delete(m.localToLastPositiveForeignUpdate, localUpdate.key)
		}
	}

	ret := []update{}
	// Update internal bookkeeping
	for fk, power := range foreignUpdates {
		m.foreignToGreatestVSCID[fk] = vscid
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
