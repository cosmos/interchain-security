package keeper

import "errors"

type LK = int
type FK = int
type VSCID = int

type update struct {
	key   FK
	power int
}

type KeyDelegation struct {
	localKeyToLastUpdate              map[LK]update
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

func (m *KeyDelegation) SetKey(lk LK, fk FK) {
	m.localKeyToCurrentForeignKey[lk] = fk
	if u, ok := m.localKeyToLastUpdate[lk]; ok {
		if 0 < u.power {
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

func (m *KeyDelegation) ComputeUpdates(vscid VSCID, localUpdates []update) (foreignUpdates []update) {
	foreignUpdates = []update{}

}
