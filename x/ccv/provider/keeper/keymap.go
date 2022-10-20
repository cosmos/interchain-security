package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/x/ccv/provider/keeper/keymap"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"
)

// TODO: use sdk prefix store instead
type KeyMapStore struct {
	Store   sdk.KVStore
	ChainID ChainID
}

func (s *KeyMapStore) SetPkToCk(pkToCk map[keymap.ProviderPubKey]keymap.ConsumerPubKey) {
	for k, v := range pkToCk {
		kbz, err := k.Marshal()
		if err != nil {
			panic(err)
		}
		vbz, err := v.Marshal()
		if err != nil {
			panic(err)
		}
		s.Store.Set(types.KeyMapPkToCkKey(s.ChainID, kbz), vbz)
	}
}
func (s *KeyMapStore) SetCkToPk(ckToPk map[keymap.ConsumerPubKey]keymap.ProviderPubKey) {
	for k, v := range ckToPk {
		kbz, err := k.Marshal()
		if err != nil {
			panic(err)
		}
		bz, err := v.Marshal()
		if err != nil {
			panic(err)
		}
		s.Store.Set(types.KeyMapCkToPkKey(s.ChainID, kbz), bz)
	}
}
func (s *KeyMapStore) SetCkToMemo(ckToMemo map[keymap.ConsumerPubKey]keymap.Memo) {
	m := ccvtypes.Memo{}
	for k, v := range ckToMemo {
		kbz, err := k.Marshal()
		if err != nil {
			panic(err)
		}
		// TODO: get rid of this hack. Not even sure if it works.
		m.Ck = &v.Ck
		m.Pk = &v.Pk
		m.Cca = v.Cca
		m.Vscid = v.Vscid
		m.Power = v.Power
		vbz, err := m.Marshal()
		if err != nil {
			panic(err)
		}
		s.Store.Set(types.KeyMapCkToMemoKey(s.ChainID, kbz), vbz)
	}
}
func (s *KeyMapStore) SetCcaToCk(ccaToCk map[keymap.StringifiedConsumerConsAddr]keymap.ConsumerPubKey) {
	for k, v := range ccaToCk {
		kbz := []byte(k)
		bz, err := v.Marshal()
		if err != nil {
			panic(err)
		}
		s.Store.Set(types.KeyMapCcaToCkKey(s.ChainID, kbz), bz)
	}
}

func (s *KeyMapStore) GetPkToCk() map[keymap.ProviderPubKey]keymap.ConsumerPubKey {
	ret := map[keymap.ProviderPubKey]keymap.ConsumerPubKey{}
	iterator := sdk.KVStorePrefixIterator(s.Store, types.KeyMapPkToCkChainPrefix(s.ChainID))

	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {

		k := keymap.ProviderPubKey{}
		err := k.Unmarshal(iterator.Key())
		if err != nil {
			panic(err)
		}
		v := keymap.ConsumerPubKey{}
		err = v.Unmarshal(iterator.Value())
		if err != nil {
			panic(err)
		}
		ret[k] = v

	}
	return ret
}
func (s *KeyMapStore) GetCkToPk() map[keymap.ConsumerPubKey]keymap.ProviderPubKey {
	ret := map[keymap.ConsumerPubKey]keymap.ProviderPubKey{}
	iterator := sdk.KVStorePrefixIterator(s.Store, types.KeyMapCkToPkChainPrefix(s.ChainID))

	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {

		k := keymap.ConsumerPubKey{}
		err := k.Unmarshal(iterator.Key())
		if err != nil {
			panic(err)
		}
		v := keymap.ConsumerPubKey{}
		err = v.Unmarshal(iterator.Value())
		if err != nil {
			panic(err)
		}
		ret[k] = v

	}
	return ret
}
func (s *KeyMapStore) GetCkToMemo() map[keymap.ConsumerPubKey]keymap.Memo {
	ret := map[keymap.ConsumerPubKey]keymap.Memo{}
	iterator := sdk.KVStorePrefixIterator(s.Store, types.KeyMapCkToMemoChainPrefix(s.ChainID))

	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {

		k := keymap.ConsumerPubKey{}
		err := k.Unmarshal(iterator.Key())
		if err != nil {
			panic(err)
		}
		v := keymap.Memo{}
		m := ccvtypes.Memo{}
		err = m.Unmarshal(iterator.Value())
		if err != nil {
			panic(err)
		}
		// TODO: remove hack, not even sure if it works.
		v.Ck = *m.Ck
		v.Pk = *m.Pk
		v.Cca = m.Cca
		v.Vscid = m.Vscid
		v.Power = m.Power
		ret[k] = v
	}
	return ret
}
func (s *KeyMapStore) GetCcaToCk() map[keymap.StringifiedConsumerConsAddr]keymap.ConsumerPubKey {
	ret := map[keymap.StringifiedConsumerConsAddr]keymap.ConsumerPubKey{}
	iterator := sdk.KVStorePrefixIterator(s.Store, types.KeyMapCcaToCkChainPrefix(s.ChainID))

	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		k := string(iterator.Key())
		v := keymap.ConsumerPubKey{}
		err := v.Unmarshal(iterator.Value())
		if err != nil {
			panic(err)
		}
		ret[k] = v

	}
	return ret
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
