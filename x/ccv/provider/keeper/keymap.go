package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/x/ccv/provider/keeper/keymap"
)

type KeyMapStore struct {
	chainID ChainID
}

func (s *KeyMapStore) GetCkToMemo() map[keymap.CK]keymap.Memo {
	return map[keymap.CK]keymap.Memo{}
}
func (s *KeyMapStore) GetPkToCk() map[keymap.PK]keymap.CK {
	return map[keymap.PK]keymap.CK{}
}
func (s *KeyMapStore) GetCkToPk() map[keymap.CK]keymap.PK {
	return map[keymap.CK]keymap.PK{}
}
func (s *KeyMapStore) SetPkToCk(e map[keymap.PK]keymap.CK) {
}
func (s *KeyMapStore) SetCkToPk(e map[keymap.CK]keymap.PK) {
}
func (s *KeyMapStore) SetCkToMemo(e map[keymap.CK]keymap.Memo) {
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
