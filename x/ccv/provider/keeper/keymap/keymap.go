package keymap

/*
TODO: I think roughly, what I need to do, to drive this thing to completion is

- [ ] more unit tests
- [ ] integration with SendValidatorUpdates
- [ ] integration with Consumer Initiated Slashing (receive request)
- [ ] integration with Consumer Initiated Slashing (send acks)
- [ ] integration with maturation (pruning)
- [ ] integration with Validator add / delete
- [ ] integration with RPC queries
- [ ] integration with msg server
- [ ] integration with pending changes
- [ ] include in diff test driver?
- [ ] include in any existing tests?

- Whenever a consumer chain is added or removed a new Keymap instance needs to be created
with a store interface which handles all of its reading and writing.
	- Need to figure out exactly where/when to add/delete consumer chain instance
	- Need to figure out exactly where/when to add/remove validator instance (with default?)


*/

import (
	"errors"
	"fmt"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"
	abci "github.com/tendermint/tendermint/abci/types"
	crypto "github.com/tendermint/tendermint/proto/tendermint/crypto"
)

type ProviderPubKey = crypto.PublicKey
type ConsumerPubKey = crypto.PublicKey
type StringifiedConsumerConsAddr = string

func consumerPubKeyToStringifiedConsumerConsAddr(ck ConsumerPubKey) StringifiedConsumerConsAddr {
	sdkCk, err := cryptocodec.FromTmProtoPublicKey(ck)
	if err != nil {
		panic("could not get public key from tm proto public key for keymap lookup")
	}
	return string(sdk.GetConsAddress(sdkCk))
}

type VSCID = uint64

type KeyMap struct {
	store    Store
	pkToCk   map[ProviderPubKey]ConsumerPubKey
	ckToPk   map[ConsumerPubKey]ProviderPubKey
	ckToMemo map[ConsumerPubKey]ccvtypes.Memo
	ccaToCk  map[StringifiedConsumerConsAddr]ConsumerPubKey
}

type Store interface {
	GetPkToCk() map[ProviderPubKey]ConsumerPubKey
	GetCkToPk() map[ConsumerPubKey]ProviderPubKey
	GetCkToMemo() map[ConsumerPubKey]ccvtypes.Memo
	GetCcaToCk() map[StringifiedConsumerConsAddr]ConsumerPubKey
	SetPkToCk(map[ProviderPubKey]ConsumerPubKey)
	SetCkToPk(map[ConsumerPubKey]ProviderPubKey)
	SetCkToMemo(map[ConsumerPubKey]ccvtypes.Memo)
	SetCcaToCk(map[StringifiedConsumerConsAddr]ConsumerPubKey)
}

func MakeKeyMap(store Store) KeyMap {
	return KeyMap{
		store: store,
	}
}

// GetAll reads all data from store
// The granularity of store access can be changed if needed for
// performance reasons.
func (e *KeyMap) GetAll() {
	e.pkToCk = e.store.GetPkToCk()
	e.ckToPk = e.store.GetCkToPk()
	e.ckToMemo = e.store.GetCkToMemo()
	e.ccaToCk = e.store.GetCcaToCk()
}

// SetAll write all data to store
// The granularity of store access can be changed if needed for
// performance reasons.
func (e *KeyMap) SetAll() {
	e.store.SetPkToCk(e.pkToCk)
	e.store.SetCkToPk(e.ckToPk)
	e.store.SetCkToMemo(e.ckToMemo)
	e.store.SetCcaToCk(e.ccaToCk)
}

// TODO:
func (e *KeyMap) SetProviderKeyToConsumerKey(pk ProviderPubKey, ck ConsumerPubKey) error {
	e.GetAll()
	if _, ok := e.ckToPk[ck]; ok {
		return errors.New(`cannot reuse key which is in use or was recently in use`)
	}
	if _, ok := e.ckToMemo[ck]; ok {
		return errors.New(`cannot reuse key which is in use or was recently in use`)
	}
	if oldCk, ok := e.pkToCk[pk]; ok {
		delete(e.ckToPk, oldCk)
	}
	e.pkToCk[pk] = ck
	e.ckToPk[ck] = pk
	e.SetAll() // TODO: Try with defer
	return nil
}

// TODO: do regular query (CK for PK)

// TODO: use found instead of error
func (e *KeyMap) GetProviderPubKeyFromConsumerPubKey(ck ConsumerPubKey) (ProviderPubKey, error) {
	e.GetAll()
	if u, ok := e.ckToMemo[ck]; ok {
		return *u.Pk, nil
	} else if pk, ok := e.ckToPk[ck]; ok {
		return pk, nil
	} else {
		return crypto.PublicKey{}, errors.New("provider key not found for consumer key")
	}
}

// TODO: use found instead of error
func (e *KeyMap) GetProviderPubKeyFromConsumerConsAddress(cca sdk.ConsAddress) (ProviderPubKey, error) {
	e.GetAll()
	ck := e.ccaToCk[string(cca)]
	return e.GetProviderPubKeyFromConsumerPubKey(ck)
}

// TODO:
func (e *KeyMap) PruneUnusedKeys(latestVscid VSCID) {
	e.GetAll()
	toDel := []ConsumerPubKey{}
	for _, u := range e.ckToMemo {
		// If the last update was a deletion (0 power) and the update
		// matured then pruning is possible.
		if u.Power == 0 && u.Vscid <= latestVscid {
			toDel = append(toDel, *u.Ck)
		}
	}
	for _, ck := range toDel {
		delete(e.ccaToCk, e.ckToMemo[ck].Cca)
		delete(e.ckToMemo, ck)
	}
	e.SetAll()
}

// TODO:
func (e *KeyMap) ComputeUpdates(vscid VSCID, providerUpdates []abci.ValidatorUpdate) (consumerUpdates []abci.ValidatorUpdate) {

	e.GetAll()

	updates := map[ProviderPubKey]int64{}

	for _, u := range providerUpdates {
		updates[u.PubKey] = u.Power
	}

	updates = e.inner(vscid, updates)

	consumerUpdates = []abci.ValidatorUpdate{}

	for ck, power := range updates {
		consumerUpdates = append(consumerUpdates, abci.ValidatorUpdate{PubKey: ck, Power: power})
	}

	e.SetAll()
	return consumerUpdates
}

// do inner work as part of ComputeUpdates
func (e *KeyMap) inner(vscid VSCID, providerUpdates map[ProviderPubKey]int64) map[ConsumerPubKey]int64 {

	pks := []ProviderPubKey{}

	// Grab provider keys where the assigned consumer key has changed
	for oldCk, u := range e.ckToMemo {
		if newCk, ok := e.pkToCk[*u.Pk]; ok {
			if oldCk != newCk && 0 < u.Power {
				pks = append(pks, *u.Pk)
			}
		}
	}
	// Grab provider keys where the validator power has changed
	for pk := range providerUpdates {
		pks = append(pks, pk)
	}

	ret := map[ConsumerPubKey]int64{}

	// Create a read only copy, so that we can query while writing
	// updates to the old version.
	ckToMemo_READ_ONLY := map[ConsumerPubKey]ccvtypes.Memo{}
	for ck, memo := range e.ckToMemo {
		ckToMemo_READ_ONLY[ck] = memo
	}

	for _, pk := range pks {
		for _, u := range ckToMemo_READ_ONLY {
			if *u.Pk == pk && 0 < u.Power {
				// For each provider key for which there was already a positive update
				// create a deletion update for the associated consumer key.
				cca := consumerPubKeyToStringifiedConsumerConsAddr(*u.Ck)
				bz, err := pk.Marshal()
				if err != nil {
					panic("woops0")
				}
				copy := crypto.PublicKey{}
				err = copy.Unmarshal(bz)
				if err != nil {
					panic("woops1")
				}
				e.ckToMemo[*u.Ck] = ccvtypes.Memo{Ck: u.Ck, Pk: &copy, Vscid: vscid, Power: 0, Cca: cca}
				e.ccaToCk[cca] = *u.Ck
				ret[*u.Ck] = 0
			}
		}
	}

	for _, pk := range pks {
		// For each provider key where there was either
		// 1) already a positive power update
		// 2) the validator power has changed (and is still positive)
		// create a change update for the associated consumer key.

		var power int64 = 0
		for _, u := range ckToMemo_READ_ONLY {
			if *u.Pk == pk && 0 < u.Power {
				// There was previously a positive power update: copy it.
				power = u.Power
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
			cca := consumerPubKeyToStringifiedConsumerConsAddr(ck)
			bz, err := pk.Marshal()
			if err != nil {
				panic("woops0")
			}
			copy := crypto.PublicKey{}
			err = copy.Unmarshal(bz)
			if err != nil {
				panic("woops1")
			}
			e.ckToMemo[ck] = ccvtypes.Memo{Ck: &ck, Pk: &copy, Vscid: vscid, Power: power, Cca: cca}
			e.ccaToCk[cca] = ck
			ret[ck] = power
		}
	}

	return ret
}

// Returns true iff internal invariants hold
func (e *KeyMap) internalInvariants() bool {

	e.GetAll()

	{
		// No two provider keys can map to the same consumer key
		// (pkToCk is sane)
		seen := map[ConsumerPubKey]bool{}
		for _, ck := range e.pkToCk {
			if seen[ck] {
				return false
			}
			seen[ck] = true
		}
	}

	{
		// all values of pkToCk is a key of ckToPk
		// (reverse lookup is always possible)
		for _, ck := range e.pkToCk {
			if _, ok := e.ckToPk[ck]; !ok {
				return false
			}
		}
	}

	{
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
	}

	{
		// If a consumer key is mapped to a provider key (currently)
		// any memo containing the same consumer key has the same
		// mapping.
		// (Ensures lookups are correct)
		for ck, pk := range e.ckToPk {
			if u, ok := e.ckToMemo[ck]; ok {
				if pk != *u.Pk {
					fmt.Println("here")

					return false
				}
			}
		}
	}

	{
		// All entries in ckToMemo have a unique consumer consensus
		// address
		seen := map[StringifiedConsumerConsAddr]bool{}
		for _, memo := range e.ckToMemo {
			if _, found := seen[memo.Cca]; found {
				return false
			}
			seen[memo.Cca] = true
		}
	}

	{
		// All entries in ckToMemo have a consumer consensus
		// address which is a key in ccaToCk
		for _, memo := range e.ckToMemo {
			if _, found := e.ccaToCk[memo.Cca]; !found {
				return false
			}
		}
	}

	{
		// All entries in ccaToCk have a unique consumer pub key
		seen := map[ConsumerPubKey]bool{}
		for _, ck := range e.ccaToCk {
			if _, found := seen[ck]; found {
				return false
			}
			seen[ck] = true
		}
	}

	{
		// All entries in ccaToCk have a consumer pub key
		// which is a key of ckToMemo
		for cca, ck := range e.ccaToCk {
			memo, found := e.ckToMemo[ck]
			if !found {
				return false
			}
			if memo.Cca != cca {
				return false
			}
		}
	}

	return true

}
