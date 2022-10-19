package keeper_test

import (
	"testing"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	providerkeeper "github.com/cosmos/interchain-security/x/ccv/provider/keeper"
	"github.com/cosmos/interchain-security/x/ccv/provider/keeper/keymap"
	"github.com/stretchr/testify/require"
	crypto "github.com/tendermint/tendermint/proto/tendermint/crypto"
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

		bytesPerKey := 32
		numKeys := 16
		if len(bz) < bytesPerKey*numKeys {
			t.Skip()
		}

		pkToCk := map[keymap.ProviderPubKey]keymap.ConsumerPubKey{}
		ckToPk := map[keymap.ConsumerPubKey]keymap.ProviderPubKey{}
		ckToMemo := map[keymap.ConsumerPubKey]keymap.Memo{}
		ccaToCk := map[keymap.StringifiedConsumerConsAddr]keymap.ConsumerPubKey{}

		keys := []crypto.PublicKey{}

		for i := 0; i < numKeys; i++ {
			pk, err := cryptocodec.ToTmProtoPublicKey(&ed25519.PubKey{Key: bz[i*bytesPerKey : (i+1)*bytesPerKey]})
			if err != nil {
				t.Fatalf("%v", err)
			}
			keys = append(keys, pk)
		}

		pkToCk[keys[0]] = keys[1]
		pkToCk[keys[2]] = keys[3]
		ckToPk[keys[4]] = keys[5]
		ckToPk[keys[6]] = keys[7]
		ckToMemo[keys[8]] = keymap.Memo{
			Ck:    keys[9],
			Pk:    keys[10],
			Cca:   string0,
			Vscid: uint64_0,
			Power: int64_0,
		}
		ckToMemo[keys[11]] = keymap.Memo{
			Ck:    keys[12],
			Pk:    keys[13],
			Cca:   string1,
			Vscid: uint64_1,
			Power: int64_1,
		}
		ccaToCk[string2] = keys[14]
		ccaToCk[string3] = keys[15]
	})
}
