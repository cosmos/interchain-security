package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/x/ccv/provider/keeper/keymap"
)

type KeyMapStore struct {
	chainID ChainID
}

func (s *KeyMapStore) GetCkToMemo() map[keymap.ConsumerPubKey]keymap.Memo {
	// TODO:
	return map[keymap.ConsumerPubKey]keymap.Memo{}
}
func (s *KeyMapStore) GetPkToCk() map[keymap.ProviderPubKey]keymap.ConsumerPubKey {
	// TODO:
	return map[keymap.ProviderPubKey]keymap.ConsumerPubKey{}
}
func (s *KeyMapStore) GetCkToPk() map[keymap.ConsumerPubKey]keymap.ProviderPubKey {
	// TODO:
	return map[keymap.ConsumerPubKey]keymap.ProviderPubKey{}
}
func (s *KeyMapStore) SetPkToCk(e map[keymap.ProviderPubKey]keymap.ConsumerPubKey) {
	// TODO:
}
func (s *KeyMapStore) SetCkToPk(e map[keymap.ConsumerPubKey]keymap.ProviderPubKey) {
	// TODO:
}
func (s *KeyMapStore) SetCkToMemo(e map[keymap.ConsumerPubKey]keymap.Memo) {
	// TODO:
}

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
