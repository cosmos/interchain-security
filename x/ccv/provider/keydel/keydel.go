package keydel

import (
	"errors"
)

type PK = int
type CK = int
type VSCID = int

type update struct {
	key   int
	power int
}

type memo struct {
	ck    CK
	pk    PK
	vscid int
	power int
}

// TODO:
// 1. Integrate into kv store.
// 2. integrate into Provider::EndBlock,
// 3. integrate with create/destroy validator
// 4. TODO: document this file

type KeyDel struct {
	pkToCk   map[PK]CK
	ckToPk   map[CK]PK
	ckToMemo map[CK]memo
}

func MakeKeyDel() KeyDel {
	return KeyDel{
		pkToCk:   map[PK]CK{},
		ckToPk:   map[CK]PK{},
		ckToMemo: map[CK]memo{},
	}
}

// TODO:
func (e *KeyDel) SetProviderKeyToConsumerKey(pk PK, ck CK) error {
	inUse := false
	if _, ok := e.ckToPk[ck]; ok {
		inUse = true
	}
	if _, ok := e.ckToMemo[ck]; ok {
		inUse = true
	}
	if inUse {
		return errors.New(`cannot reuse key which is in use or was recently in use`)
	}
	if oldCk, ok := e.pkToCk[pk]; ok {
		delete(e.ckToPk, oldCk)
	}
	e.pkToCk[pk] = ck
	e.ckToPk[ck] = pk
	return nil
}

// TODO:
func (e *KeyDel) GetProviderKey(ck CK) (PK, error) {
	if u, ok := e.ckToMemo[ck]; ok {
		return u.pk, nil
	} else if pk, ok := e.ckToPk[ck]; ok {
		return pk, nil
	} else {
		return -1, errors.New("provider key not found for consumer key")
	}
}

// TODO:
func (e *KeyDel) PruneUnusedKeys(latestVscid VSCID) {
	toDel := []CK{}
	for _, u := range e.ckToMemo {
		// If the last update was a deletion (0 power) and the update
		// matured then pruning is possible.
		if u.power == 0 && u.vscid <= latestVscid {
			toDel = append(toDel, u.ck)
		}
	}
	for _, ck := range toDel {
		delete(e.ckToMemo, ck)
	}
}

// TODO:
func (e *KeyDel) ComputeUpdates(vscid VSCID, providerUpdates []update) (consumerUpdates []update) {

	updates := map[PK]int{}

	for _, u := range providerUpdates {
		updates[u.key] = u.power
	}

	updates = e.inner(vscid, updates)

	consumerUpdates = []update{}

	for ck, power := range updates {
		consumerUpdates = append(consumerUpdates, update{key: ck, power: power})
	}

	return consumerUpdates
}

// do inner work as part of ComputeUpdates
func (e *KeyDel) inner(vscid VSCID, providerUpdates map[PK]int) map[CK]int {

	pks := []PK{}

	// Grab provider keys where the assigned consumer key has changed
	for oldCk, u := range e.ckToMemo {
		if newCk, ok := e.pkToCk[u.pk]; ok {
			if oldCk != newCk && 0 < u.power {
				pks = append(pks, u.pk)
			}
		}
	}
	// Grab provider keys where the validator power has changed
	for pk := range providerUpdates {
		pks = append(pks, pk)
	}

	ret := map[CK]int{}

	// Create a read only copy, so that we can query while writing
	// updates to the old version.
	ckToMemo_READ_ONLY := map[CK]memo{}
	for ck, memo := range e.ckToMemo {
		ckToMemo_READ_ONLY[ck] = memo
	}

	for _, pk := range pks {
		for _, u := range ckToMemo_READ_ONLY {
			if u.pk == pk && 0 < u.power {
				// For each provider key for which there was already a positive update
				// create a deletion update for the associated consumer key.
				e.ckToMemo[u.ck] = memo{ck: u.ck, pk: pk, vscid: vscid, power: 0}
				ret[u.ck] = 0
			}
		}
	}

	for _, pk := range pks {
		// For each provider key where there was either
		// 1) already a positive power update
		// 2) the validator power has changed (and is still positive)
		// create a change update for the associated consumer key.

		power := 0
		for _, u := range ckToMemo_READ_ONLY {
			if u.pk == pk && 0 < u.power {
				// There was previously a positive power update: copy it.
				power = u.power
			}
		}
		// There is a new validator power: use it.
		if newPower, ok := providerUpdates[pk]; ok {
			power = newPower
		}
		// Only ship update with positive powers. Zero power updates (deletions)
		// are handled in earlier block.
		if 0 < power {
			ck := e.pkToCk[pk]
			e.ckToMemo[ck] = memo{ck: ck, pk: pk, vscid: vscid, power: power}
			ret[ck] = power
		}
	}

	return ret
}

// Returns true iff internal invariants hold
func (e *KeyDel) internalInvariants() bool {

	// No two provider keys can map to the same consumer key
	// (pkToCk is sane)
	seen := map[CK]bool{}
	for _, ck := range e.pkToCk {
		if seen[ck] {
			return false
		}
		seen[ck] = true
	}

	// all values of pkToCk is a key of ckToPk
	// (reverse lookup is always possible)
	for _, ck := range e.pkToCk {
		if _, ok := e.ckToPk[ck]; !ok {
			return false
		}
	}

	// All consumer keys mapping to provider keys are actually
	// mapped to by the provider key.
	// (ckToPk is sane)
	for ck := range e.ckToPk {
		good := false
		for _, candidateCk := range e.pkToCk {
			if candidateCk == ck {
				good = true
				break
			}
		}
		if !good {
			return false
		}
	}

	// If a consumer key is mapped to a provider key (currently)
	// any memo containing the same consumer key has the same
	// mapping.
	// (Ensures lookups are correct)
	for ck, pk := range e.ckToPk {
		if u, ok := e.ckToMemo[ck]; ok {
			if pk != u.pk {
				return false
			}
		}
	}

	return true

}
