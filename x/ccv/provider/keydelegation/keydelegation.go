package keydelegation

import "errors"

type LK = int
type FK = int
type VSCID = int

type update struct {
	key   FK
	power int
}

type KeyDelegation struct {
	// TODO: how to GC this?
	localKeyToLastUpdate map[LK]update
	// TODO: how to GC this?
	localKeyToCurrentForeignKey       map[LK]FK
	foreignKeyToLocalKey              map[FK]LK
	foreignKeyToVscidWhenLastSent     map[FK]VSCID
	localKeysForWhichUpdateMustBeSent []LK
}

func MakeKeyDelegation() KeyDelegation {
	return KeyDelegation{
		localKeyToLastUpdate:              map[LK]update{},
		localKeyToCurrentForeignKey:       map[LK]FK{},
		foreignKeyToLocalKey:              map[FK]LK{},
		foreignKeyToVscidWhenLastSent:     map[FK]VSCID{},
		localKeysForWhichUpdateMustBeSent: []LK{},
	}
}

func (m *KeyDelegation) SetForeignKey(lk LK, fk FK) {
	if currFk, ok := m.localKeyToCurrentForeignKey[lk]; ok {
		if currFk == fk {
			return
		}
	}
	m.localKeyToCurrentForeignKey[lk] = fk
	if u, ok := m.localKeyToLastUpdate[lk]; ok {
		if 0 < u.power {
			// If last update had positive power then the consumer is aware of the old key
			// so a deletion update must be sent.
			m.localKeysForWhichUpdateMustBeSent = append(m.localKeysForWhichUpdateMustBeSent, lk)
		}
	}
}

func (m *KeyDelegation) GetLocalKey(fk FK) (LK, error) {
	if lk, ok := m.foreignKeyToLocalKey[fk]; ok {
		return lk, nil
	} else {
		return -1, errors.New("nope")
	}
}

func (m *KeyDelegation) Prune(mostRecentlyMaturedVscid VSCID) {
	toRemove := []FK{}
	for fk, vscid := range m.foreignKeyToVscidWhenLastSent {
		if vscid <= mostRecentlyMaturedVscid {
			toRemove = append(toRemove, fk)
		}
	}
	for _, fk := range toRemove {
		delete(m.foreignKeyToVscidWhenLastSent, fk)
		delete(m.foreignKeyToLocalKey, fk)
	}
}

func (m *KeyDelegation) ComputeUpdates(vscid VSCID, localUpdates []update) (foreignUpdates []update) {
	foreignUpdates = []update{}

	// Create any updates for validators whose power did not change
	for _, lk := range m.localKeysForWhichUpdateMustBeSent {
		currKey := m.localKeyToCurrentForeignKey[lk]
		u := m.localKeyToLastUpdate[lk]
		// Create an update which will delete the validator for the old key
		foreignUpdates = append(foreignUpdates, update{key: u.key, power: 0})
		// Create an update which will add the validator for the new key
		foreignUpdates = append(foreignUpdates, update{key: currKey, power: u.power})
	}
	m.localKeysForWhichUpdateMustBeSent = []LK{}

	// Create any updates for validators whose powers did change
	for _, u := range localUpdates {
		// Check if the consumer has an old key
		if lastU, ok := m.localKeyToLastUpdate[u.key]; ok {
			// Create an update which will delete the validator for the old key
			foreignUpdates = append(foreignUpdates, update{key: lastU.key, power: 0})
		}
		currKey := m.localKeyToCurrentForeignKey[u.key]
		// Create an update which will add/update the validator for the current key
		foreignUpdates = append(foreignUpdates, update{key: currKey, power: u.power})
	}

	// Update internal bookkeeping
	for _, u := range foreignUpdates {
		m.foreignKeyToVscidWhenLastSent[u.key] = vscid
		m.localKeyToLastUpdate[m.foreignKeyToLocalKey[u.key]] = u
	}

	return foreignUpdates
}
