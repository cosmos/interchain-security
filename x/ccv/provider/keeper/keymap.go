package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/x/ccv/provider/keeper/keymap"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"
)

type KeyMapStore struct {
	store   sdk.KVStore
	chainID ChainID
}

// TODO: pickup: write these methods,
// will need to change the types...Key methods to accept more data
// for the GET, will need to use a store iterator to read everything in
// for the SET, will need to iterate over the map and just write everything

func (s *KeyMapStore) GetPkToCk() map[keymap.ProviderPubKey]keymap.ConsumerPubKey {
	// bz := s.store.Get(types.KeyMapPkToCkKey(s.chainID))
	panic("no im")
}
func (s *KeyMapStore) GetCkToPk() map[keymap.ConsumerPubKey]keymap.ProviderPubKey {
	// bz := s.store.Get(types.KeyMapCkToPkKey(s.chainID))
	panic("no im")
}
func (s *KeyMapStore) GetCkToMemo() map[keymap.ConsumerPubKey]keymap.Memo {
	// bz := s.store.Get(types.KeyMapCkToMemoKey(s.chainID))
	panic("no im")
}
func (s *KeyMapStore) GetCcaToCk() map[keymap.StringifiedConsumerConsAddr]keymap.ConsumerPubKey {
	// bz := s.store.Get(types.KeyMapCcaToCkKey(s.chainID))
	panic("no im")
}
func (s *KeyMapStore) SetPkToCk(pkToCk map[keymap.ProviderPubKey]keymap.ConsumerPubKey) {
	for k, v := range pkToCk {
		bz, err := v.Marshal()
		if err != nil {
			panic(err)
		}
		s.store.Set(types.KeyMapPkToCkKey(s.chainID, k), bz)
	}
}
func (s *KeyMapStore) SetCkToPk(ckToPk map[keymap.ConsumerPubKey]keymap.ProviderPubKey) {
	for k, v := range ckToPk {
		bz, err := v.Marshal()
		if err != nil {
			panic(err)
		}
		s.store.Set(types.KeyMapCkToPkKey(s.chainID, k), bz)
	}
}
func (s *KeyMapStore) SetCkToMemo(ckToMemo map[keymap.ConsumerPubKey]keymap.Memo) {
	m := ccvtypes.Memo{}
	for k, v := range ckToMemo {
		// TODO: get rid of this hack. Not even sure if it works.
		m.Ck = &v.Ck
		m.Pk = &v.Pk
		m.Cca = v.Cca
		m.Vscid = v.Vscid
		m.Power = v.Power
		bz, err := m.Marshal()
		if err != nil {
			panic(err)
		}
		s.store.Set(types.KeyMapCkToMemoKey(s.chainID, k), bz)
	}
}
func (s *KeyMapStore) SetCcaToCk(ccaToCk map[keymap.StringifiedConsumerConsAddr]keymap.ConsumerPubKey) {
	for k, v := range ccaToCk {
		bz, err := v.Marshal()
		if err != nil {
			panic(err)
		}
		s.store.Set(types.KeyMapCcaToCkKey(s.chainID, k), bz)
	}
}

/*
// SetPendingConsumerRemovalProp stores a pending proposal to remove and stop a consumer chain
func (k Keeper) SetPendingConsumerRemovalProp(ctx sdk.Context, chainID string, timestamp time.Time) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.PendingCRPKey(timestamp, chainID), []byte{})
}
*/

func (k Keeper) addKeyMap(chainID ChainID) {

}

func (k Keeper) delKeyMap(chainID ChainID) {

}

func (k Keeper) loadKeyMaps(ctx sdk.Context) {
	k.keymaps = map[ChainID]*keymap.KeyMap{}
	k.IterateConsumerChains(ctx, func(ctx sdk.Context, chainID, _ string) (stop bool) {
		store := KeyMapStore{ctx.KVStore(k.storeKey), chainID}
		km := keymap.MakeKeyMap(&store)
		k.keymaps[chainID] = &km
		return false
	})
}
