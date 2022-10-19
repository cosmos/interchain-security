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
	f.Fuzz(func(t *testing.T, chainID string, bz []byte,
		string0 string,
		string1 string,
		string2 string,
		string3 string,
		int64_0 int64,
		int64_1 int64,
		uint64_0 uint64,
		uint64_1 uint64,
	) {
		keeperParams := testkeeper.NewInMemKeeperParams(t)
		_, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, keeperParams)
		defer ctrl.Finish()
		store := providerkeeper.KeyMapStore{ctx.KVStore(keeperParams.StoreKey), chainID}
		km := keymap.MakeKeyMap(&store)
		_ = km

		if len(bz) < 32 {
			t.Skip()
		}

		pkToCk := map[keymap.ProviderPubKey]keymap.ConsumerPubKey{}
		ckToPk := map[keymap.ConsumerPubKey]keymap.ProviderPubKey{}
		ckToMemo := map[keymap.ConsumerPubKey]keymap.Memo{}
		ccaToCk := map[keymap.StringifiedConsumerConsAddr]keymap.ConsumerPubKey{}

		pk0, err := cryptocodec.ToTmProtoPublicKey(&ed25519.PubKey{Key: bz[0:32]})
		if err != nil {
			t.Fatalf("%v", err)
		}
		pk1, _ := cryptocodec.ToTmProtoPublicKey(&ed25519.PubKey{Key: bz[0:32]})
		pk2, _ := cryptocodec.ToTmProtoPublicKey(&ed25519.PubKey{Key: bz[0:32]})
		pk3, _ := cryptocodec.ToTmProtoPublicKey(&ed25519.PubKey{Key: bz[0:32]})
		pk4, _ := cryptocodec.ToTmProtoPublicKey(&ed25519.PubKey{Key: bz[0:32]})
		pk5, _ := cryptocodec.ToTmProtoPublicKey(&ed25519.PubKey{Key: bz[0:32]})
		pk6, _ := cryptocodec.ToTmProtoPublicKey(&ed25519.PubKey{Key: bz[0:32]})
		pk7, _ := cryptocodec.ToTmProtoPublicKey(&ed25519.PubKey{Key: bz[0:32]})
		pk8, _ := cryptocodec.ToTmProtoPublicKey(&ed25519.PubKey{Key: bz[0:32]})
		pk9, _ := cryptocodec.ToTmProtoPublicKey(&ed25519.PubKey{Key: bz[0:32]})
		pk10, _ := cryptocodec.ToTmProtoPublicKey(&ed25519.PubKey{Key: bz[0:32]})
		pk11, _ := cryptocodec.ToTmProtoPublicKey(&ed25519.PubKey{Key: bz[0:32]})
		pk12, _ := cryptocodec.ToTmProtoPublicKey(&ed25519.PubKey{Key: bz[0:32]})
		pk13, _ := cryptocodec.ToTmProtoPublicKey(&ed25519.PubKey{Key: bz[0:32]})
		pk14, _ := cryptocodec.ToTmProtoPublicKey(&ed25519.PubKey{Key: bz[0:32]})
		pk15, _ := cryptocodec.ToTmProtoPublicKey(&ed25519.PubKey{Key: bz[0:32]})
		pkToCk[pk0] = pk1
		pkToCk[pk2] = pk3
		ckToPk[pk4] = pk5
		ckToPk[pk6] = pk7
		ckToMemo[pk8] = keymap.Memo{
			Ck:    pk9,
			Pk:    pk10,
			Cca:   string0,
			Vscid: uint64_0,
			Power: int64_0,
		}
		ckToMemo[pk11] = keymap.Memo{
			Ck:    pk12,
			Pk:    pk13,
			Cca:   string1,
			Vscid: uint64_1,
			Power: int64_1,
		}
		ccaToCk[string2] = pk14
		ccaToCk[string3] = pk15
	})
}
