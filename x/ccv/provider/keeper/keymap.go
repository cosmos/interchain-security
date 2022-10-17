package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/x/ccv/provider/keeper/keymap"
)

type KeyMapStore struct {
	chainID ChainID
}

func (s KeyMapStore) getPkToCk() map[keymap.PK]keymap.CK {
	_ = s
	// TODO: implement
	panic("not implemented")
}

func (s KeyMapStore) getCkToPk() map[keymap.CK]keymap.PK {
	_ = s
	// TODO: implement
	panic("not implemented")
}

func (s KeyMapStore) getCkToMemo() map[keymap.CK]keymap.Memo {
	_ = s
	// TODO: implement
	panic("not implemented")
}

func (s KeyMapStore) setPkToCk(e map[keymap.PK]keymap.CK) {
	_ = s
	// TODO: implement
	panic("not implemented")
}

func (s KeyMapStore) setCkToPk(e map[keymap.CK]keymap.PK) {
	_ = s
	// TODO: implement
	panic("not implemented")
}

func (s KeyMapStore) setCkToMemo(e map[keymap.CK]keymap.Memo) {
	_ = s
	// TODO: implement
	panic("not implemented")
}

func (k Keeper) addKeyMapForConsumer(chainID ChainID) {

}

func (k Keeper) delKeyMapForConsumer(chainID ChainID) {

}

func (k Keeper) loadKeyMaps(ctx sdk.Context) {

	k.keymaps = map[ChainID]keymap.KeyMap{}
	k.IterateConsumerChains(ctx, func(ctx sdk.Context, chainID, clientID string) (stop bool) {
		store := KeyMapStore{chainID}
		k.keymaps[chainID] = keymap.MakeKeyMap(store)
		return false
	})

}
