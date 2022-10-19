package keeper_test

import (
	"testing"

	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	providerkeeper "github.com/cosmos/interchain-security/x/ccv/provider/keeper"
	"github.com/cosmos/interchain-security/x/ccv/provider/keeper/keymap"
	"github.com/stretchr/testify/require"
)

func TestKeyMapSerializationAndDeserialization(t *testing.T) {
}

func TestKeyMapLoadEmpty(t *testing.T) {
	keeperParams := testkeeper.NewInMemKeeperParams(t)
	_, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, keeperParams)
	store := providerkeeper.KeyMapStore{ctx.KVStore(keeperParams.StoreKey), chainID}
	km := keymap.MakeKeyMap(&store)
	defer ctrl.Finish()
	require.Zero(t, km.)
}
func FuzzKeyMapSerializationAndDeserialization(f *testing.F) {
	f.Fuzz(func(t *testing.T, chainID string, bz []byte) {
		keeperParams := testkeeper.NewInMemKeeperParams(t)
		_, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, keeperParams)
		store := providerkeeper.KeyMapStore{ctx.KVStore(keeperParams.StoreKey), chainID}
		km := keymap.MakeKeyMap(&store)
		defer ctrl.Finish()
		// t.Skip()
	})
}
