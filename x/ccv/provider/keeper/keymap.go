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

func (s *KeyMapStore) GetPkToCk() map[keymap.ProviderPubKey]keymap.ConsumerPubKey {
	// bz := s.store.Get(types.KeyMapPkToCkKey(s.chainID))
	panic("no im")
}
func (s *KeyMapStore) GetCkToPk() map[keymap.ConsumerPubKey]keymap.ProviderPubKey {
	// bz := s.store.Get(types.KeyMapCkToPkKey(s.chainID))
	panic("no im")
}
func (s *KeyMapStore) GetCkToMemo() map[keymap.ConsumerPubKey]ccvtypes.Memo {
	// bz := s.store.Get(types.KeyMapCkToMemoKey(s.chainID))
	panic("no im")
}
func (s *KeyMapStore) GetCcaToCk() map[keymap.StringifiedConsumerConsAddr]keymap.ConsumerPubKey {
	// bz := s.store.Get(types.KeyMapCcaToCkKey(s.chainID))
	panic("no im")
}
func (s *KeyMapStore) SetPkToCk(e map[keymap.ProviderPubKey]keymap.ConsumerPubKey) {
	bz := []byte{}
	s.store.Set(types.KeyMapPkToCkKey(s.chainID), bz)
	panic("no im")
}
func (s *KeyMapStore) SetCkToPk(e map[keymap.ConsumerPubKey]keymap.ProviderPubKey) {
	bz := []byte{}
	s.store.Set(types.KeyMapCkToPkKey(s.chainID), bz)
	panic("no im")
}
func (s *KeyMapStore) SetCkToMemo(e map[keymap.ConsumerPubKey]ccvtypes.Memo) {
	bz := []byte{}
	s.store.Set(types.KeyMapCkToMemoKey(s.chainID), bz)
	panic("no im")
}
func (s *KeyMapStore) SetCcaToCk(ccaToCk map[keymap.StringifiedConsumerConsAddr]keymap.ConsumerPubKey) {
	bz := []byte{}
	s.store.Set(types.KeyMapCcaToCkKey(s.chainID), bz)
	panic("no im")
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
