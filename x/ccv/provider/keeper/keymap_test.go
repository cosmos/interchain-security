package keeper_test

import (
	"testing"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
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
	defer ctrl.Finish()
	chainID := "foobar"
	store := providerkeeper.KeyMapStore{ctx.KVStore(keeperParams.StoreKey), chainID}
	km := keymap.MakeKeyMap(&store)

	// Do a query operation to trigger a store load TODO: just use GetAll() if it ends up being public
	_, err := km.GetProviderPubKeyFromConsumerPubKey(keymap.ConsumerPubKey{})
	// It should be an error because nothing should be there TODO: change
	require.Error(t, err)
	// Check that all the data is initialized empty
	require.NotNil(t, km.PkToCk)
	require.NotNil(t, km.CkToPk)
	require.NotNil(t, km.CkToMemo)
	require.NotNil(t, km.CcaToCk)
	require.Zero(t, len(km.PkToCk))
	require.Zero(t, len(km.CkToPk))
	require.Zero(t, len(km.CkToMemo))
	require.Zero(t, len(km.CcaToCk))
}
func FuzzKeyMapSerializationAndDeserialization(f *testing.F) {
	f.Fuzz(func(t *testing.T, chainID string, bz []byte) {
		keeperParams := testkeeper.NewInMemKeeperParams(t)
		_, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, keeperParams)
		defer ctrl.Finish()
		store := providerkeeper.KeyMapStore{ctx.KVStore(keeperParams.StoreKey), chainID}
		km := keymap.MakeKeyMap(&store)
		_ = km
		// t.Skip()

		pkToCk := map[keymap.ProviderPubKey]keymap.ConsumerPubKey{}
		ckToPk := map[keymap.ConsumerPubKey]keymap.ProviderPubKey{}
		ckToMemo := map[keymap.ConsumerPubKey]keymap.Memo{}
		ccaToCk := map[keymap.StringifiedConsumerConsAddr]keymap.ConsumerPubKey{}
		// x := keymap.ProviderPubKey{}
		pk, err := cryptocodec.ToTmProtoPublicKey(&ed25519.PubKey{Key: bz[0:32]})

	})
}
