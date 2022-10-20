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

func (s *KeyMapStore) SetPkToCk(pkToCk map[keymap.StringifiedProviderPubKey]keymap.ConsumerPubKey) {
	for k, v := range pkToCk {
		kbz := []byte(k)
		vbz, err := v.Marshal()
		if err != nil {
			panic(err)
		}
		s.Store.Set(types.KeyMapPkToCkKey(s.ChainID, kbz), vbz)
	}
}
func (s *KeyMapStore) SetCkToPk(ckToPk map[keymap.StringifiedConsumerPubKey]keymap.ProviderPubKey) {
	for k, v := range ckToPk {
		kbz := []byte(k)
		vbz, err := v.Marshal()
		if err != nil {
			panic(err)
		}
		s.Store.Set(types.KeyMapCkToPkKey(s.ChainID, kbz), vbz)
	}
}
func (s *KeyMapStore) SetCkToMemo(ckToMemo map[keymap.StringifiedConsumerPubKey]keymap.Memo) {
	m := ccvtypes.Memo{}
	for k, v := range ckToMemo {
		kbz := []byte(k)
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
		vbz, err := v.Marshal()
		if err != nil {
			panic(err)
		}
		s.Store.Set(types.KeyMapCcaToCkKey(s.ChainID, kbz), vbz)
	}
}

func (s *KeyMapStore) GetPkToCk() map[keymap.StringifiedProviderPubKey]keymap.ConsumerPubKey {
	ret := map[keymap.StringifiedProviderPubKey]keymap.ConsumerPubKey{}
	prefix := types.KeyMapPkToCkChainPrefix(s.ChainID)
	iterator := sdk.KVStorePrefixIterator(s.Store, prefix)

	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		k := string(iterator.Key()[len(prefix):])
		v := keymap.ConsumerPubKey{}
		err := v.Unmarshal(iterator.Value())
		if err != nil {
			panic(err)
		}
		ret[k] = v

	}
	return ret
}
func (s *KeyMapStore) GetCkToPk() map[keymap.StringifiedConsumerPubKey]keymap.ProviderPubKey {
	ret := map[keymap.StringifiedConsumerPubKey]keymap.ProviderPubKey{}
	prefix := types.KeyMapCkToPkChainPrefix(s.ChainID)
	iterator := sdk.KVStorePrefixIterator(s.Store, prefix)

	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		k := string(iterator.Key()[len(prefix):])
		v := keymap.ConsumerPubKey{}
		err := v.Unmarshal(iterator.Value())
		if err != nil {
			panic(err)
		}
		ret[k] = v

	}
	return ret
}
func (s *KeyMapStore) GetCkToMemo() map[keymap.StringifiedConsumerPubKey]keymap.Memo {
	ret := map[keymap.StringifiedConsumerPubKey]keymap.Memo{}
	prefix := types.KeyMapCkToMemoChainPrefix(s.ChainID)
	iterator := sdk.KVStorePrefixIterator(s.Store, prefix)

	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {

		k := string(iterator.Key()[len(prefix):])
		v := keymap.Memo{}
		m := ccvtypes.Memo{}
		err := m.Unmarshal(iterator.Value())
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
	prefix := types.KeyMapCcaToCkChainPrefix(s.ChainID)
	iterator := sdk.KVStorePrefixIterator(s.Store, prefix)

	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		k := string(iterator.Key()[len(prefix):])
		v := keymap.ConsumerPubKey{}
		err := v.Unmarshal(iterator.Value())
		if err != nil {
			panic(err)
		}
		ret[k] = v

	}
	return ret
}

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
