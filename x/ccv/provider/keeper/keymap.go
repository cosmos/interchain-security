package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/x/ccv/provider/keeper/keymap"
)

type KeyMapStore struct {
	chainID ChainID
}

func (s *KeyMapStore) GetPkToCk() map[keymap.ProviderPubKey]keymap.ConsumerPubKey {
	panic("no im")
}
func (s *KeyMapStore) GetCkToPk() map[keymap.ConsumerPubKey]keymap.ProviderPubKey {
	panic("no im")
}
func (s *KeyMapStore) GetCkToMemo() map[keymap.ConsumerPubKey]keymap.Memo {
	panic("no im")
}
func (s *KeyMapStore) GetCcaToCk() map[keymap.StringifiedConsumerConsAddr]keymap.ConsumerPubKey {
	panic("no im")
}
func (s *KeyMapStore) SetPkToCk(e map[keymap.ProviderPubKey]keymap.ConsumerPubKey) {
	panic("no im")
}
func (s *KeyMapStore) SetCkToPk(e map[keymap.ConsumerPubKey]keymap.ProviderPubKey) {
	panic("no im")
}
func (s *KeyMapStore) SetCkToMemo(e map[keymap.ConsumerPubKey]keymap.Memo) {
	panic("no im")
}
func (s *KeyMapStore) SetCcaToCk(ccaToCk map[keymap.StringifiedConsumerConsAddr]keymap.ConsumerPubKey) {
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
		store := KeyMapStore{chainID}
		km := keymap.MakeKeyMap(&store)
		k.keymaps[chainID] = &km
		return false
	})
}
