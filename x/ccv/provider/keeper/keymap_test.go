package keeper_test

import (
	"testing"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/simapp"
	sdk "github.com/cosmos/cosmos-sdk/types"

	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	providerkeeper "github.com/cosmos/interchain-security/x/ccv/provider/keeper"
	"github.com/cosmos/interchain-security/x/ccv/provider/keeper/keymap"
	"github.com/stretchr/testify/require"
	crypto "github.com/tendermint/tendermint/proto/tendermint/crypto"
)

func TestKeyMapLookupA(t *testing.T) {
	keys := simapp.CreateTestPubKeys(1)
	key, err := cryptocodec.ToTmProtoPublicKey(keys[0])
	require.NoError(t, err)
	m := map[crypto.PublicKey]int{}
	m[key] = 42
	_, ok := m[key]
	require.True(t, ok)
}

func TestKeyMapLookupB(t *testing.T) {
	keys := simapp.CreateTestPubKeys(1)
	key, err := cryptocodec.ToTmProtoPublicKey(keys[0])
	require.NoError(t, err)
	m := map[crypto.PublicKey]int{}
	m[key] = 42
	keys1 := simapp.CreateTestPubKeys(1)
	key1, err := cryptocodec.ToTmProtoPublicKey(keys1[0])
	require.Equal(t, key, key1)
	require.NoError(t, err)
	_, ok := m[key1]
	require.True(t, ok)
}

func TestKeyBasic(t *testing.T) {
	keys := simapp.CreateTestPubKeys(1)
	kWrite, err := cryptocodec.ToTmProtoPublicKey(keys[0])
	if err != nil {
		panic("could not create tendermint test keys")
	}
	bz, err := kWrite.Marshal()
	require.NoError(t, err)
	kRead := crypto.PublicKey{}
	err = kRead.Unmarshal(bz)
	require.NoError(t, err)
	require.Equal(t, kWrite, kRead)
}

func TestKeyBasicWithStore(t *testing.T) {
	keeperParams := testkeeper.NewInMemKeeperParams(t)
	_, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, keeperParams)
	defer ctrl.Finish()
	store := ctx.KVStore(keeperParams.StoreKey)

	keys := simapp.CreateTestPubKeys(1)
	kWrite, err := cryptocodec.ToTmProtoPublicKey(keys[0])
	if err != nil {
		panic("could not create tendermint test keys")
	}
	bzWrite, err := kWrite.Marshal()
	require.NoError(t, err)

	storeKey := []byte{42}
	store.Set(storeKey, bzWrite)
	bzRead := store.Get(storeKey)

	kRead := crypto.PublicKey{}
	err = kRead.Unmarshal(bzRead)
	require.NoError(t, err)
	require.Equal(t, kWrite, kRead)
}

func TestKeyBasicWithStorePrefixIterator(t *testing.T) {
	keeperParams := testkeeper.NewInMemKeeperParams(t)
	_, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, keeperParams)
	defer ctrl.Finish()
	store := ctx.KVStore(keeperParams.StoreKey)

	keys := simapp.CreateTestPubKeys(1)
	kWrite, err := cryptocodec.ToTmProtoPublicKey(keys[0])
	if err != nil {
		panic("could not create tendermint test keys")
	}
	bzWrite, err := kWrite.Marshal()
	require.NoError(t, err)

	storePrefix := []byte{42}
	store.Set(append(storePrefix, bzWrite...), []byte{})

	iterator := sdk.KVStorePrefixIterator(store, storePrefix)

	var bzRead []byte
	defer iterator.Close()
	for ; iterator.Valid(); iterator.Next() {
		bzRead = iterator.Key()[len(storePrefix):]
	}

	kRead := crypto.PublicKey{}
	err = kRead.Unmarshal(bzRead)
	require.NoError(t, err)
	require.Equal(t, kWrite, kRead)
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

func compareForEquality(t *testing.T,
	km keymap.KeyMap,
	pkToCk map[keymap.StringifiedProviderPubKey]keymap.ConsumerPubKey,
	ckToPk map[keymap.StringifiedConsumerPubKey]keymap.ProviderPubKey,
	ckToMemo map[keymap.StringifiedConsumerPubKey]keymap.Memo,
	ccaToCk map[keymap.StringifiedConsumerConsAddr]keymap.ConsumerPubKey) {

	require.Equal(t, len(pkToCk), len(km.PkToCk))
	require.Equal(t, len(ckToPk), len(km.CkToPk))
	require.Equal(t, len(ckToMemo), len(km.CkToMemo))
	require.Equal(t, len(ccaToCk), len(km.CcaToCk))

	for k, v := range ccaToCk {
		require.Equal(t, v, km.CcaToCk[k])
	}
	for k, v := range pkToCk {
		require.Equal(t, v, km.PkToCk[k])
	}
	for k, v := range ckToPk {
		require.Equal(t, v, km.CkToPk[k])
	}
	for k, v := range ckToMemo {
		m := km.CkToMemo[k]
		require.Equal(t, v.Pk, m.Pk)
		require.Equal(t, v.Ck, m.Ck)
		require.Equal(t, v.Cca, m.Cca)
		require.Equal(t, v.Vscid, m.Vscid)
		require.Equal(t, v.Power, m.Power)
	}
}

func checkCorrectSerializationAndDeserialization(t *testing.T,
	chainID string, keys []crypto.PublicKey,
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

	pkToCk := map[keymap.StringifiedProviderPubKey]keymap.ConsumerPubKey{}
	ckToPk := map[keymap.StringifiedConsumerPubKey]keymap.ProviderPubKey{}
	ckToMemo := map[keymap.StringifiedConsumerPubKey]keymap.Memo{}
	ccaToCk := map[keymap.StringifiedConsumerConsAddr]keymap.ConsumerPubKey{}

	pkToCk[keymap.StringifyPubKey(keys[0])] = keys[1]
	pkToCk[keymap.StringifyPubKey(keys[2])] = keys[3]
	ckToPk[keymap.StringifyPubKey(keys[4])] = keys[5]
	ckToPk[keymap.StringifyPubKey(keys[6])] = keys[7]
	ckToMemo[keymap.StringifyPubKey(keys[8])] = keymap.Memo{
		Ck:    keys[9],
		Pk:    keys[10],
		Cca:   string0,
		Vscid: uint64_0,
		Power: int64_0,
	}
	ckToMemo[keymap.StringifyPubKey(keys[11])] = keymap.Memo{
		Ck:    keys[12],
		Pk:    keys[13],
		Cca:   string1,
		Vscid: uint64_1,
		Power: int64_1,
	}
	ccaToCk[string2] = keys[14]
	ccaToCk[string3] = keys[15]

	{
		// Use one KeyMap instance to serialize the data
		store := providerkeeper.KeyMapStore{ctx.KVStore(keeperParams.StoreKey), chainID}
		km := keymap.MakeKeyMap(&store)
		km.PkToCk = pkToCk
		km.CkToPk = ckToPk
		km.CkToMemo = ckToMemo
		km.CcaToCk = ccaToCk
		km.SetAll()
	}

	// Use another KeyMap instance to deserialize the data
	store := providerkeeper.KeyMapStore{ctx.KVStore(keeperParams.StoreKey), chainID}
	km := keymap.MakeKeyMap(&store)
	km.GetAll()

	// Check that the data is the same

	compareForEquality(t, km, pkToCk, ckToPk, ckToMemo, ccaToCk)
}

func TestKeyMapSerializationAndDeserialization(t *testing.T) {

	getKeys := func() (ret []crypto.PublicKey) {
		// TODO: deduplicate with similar code in keymap/
		totalNumKeys := 16
		keys := simapp.CreateTestPubKeys(totalNumKeys)
		for i := 0; i < totalNumKeys; i++ {
			k, err := cryptocodec.ToTmProtoPublicKey(keys[i])
			if err != nil {
				panic("could not create tendermint test keys")
			}
			ret = append(ret, k)
		}
		return ret
	}

	checkCorrectSerializationAndDeserialization(t, "foobar", getKeys(),
		"string0",
		"string1",
		"string2",
		"string3",
		42,
		43,
		44,
		45,
	)

}

/*
// TODO: another idea here would be to use the generation already used for business

// logic testing in keymap/ , but the seeds there are less general.
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

		// Check viability
		// If not viable: skip the test
		bytesPerKey := 64
		numKeys := 16
		if len(bz) < bytesPerKey*numKeys {
			t.Skip()
		}

		getKeys := func() (ret []crypto.PublicKey) {
			for i := 0; i < numKeys; i++ {
				seed := bz[i*bytesPerKey : (i+1)*bytesPerKey]
				// TODO: deduplicate with the function in seed gen test for diff driver
				//lint:ignore SA1019 We don't care because this is only a test.
				privKey := mock.PV{PrivKey: &cosmosEd25519.PrivKey{Key: cryptoEd25519.NewKeyFromSeed(seed)}}
				pubKey, err := privKey.GetPubKey()
				if err != nil {
					t.Fatalf("%v", err)
				}
				sdkVer, err := cryptocodec.FromTmPubKeyInterface(pubKey)
				if err != nil {
					t.Fatalf("%v", err)
				}
				pk, err := cryptocodec.ToTmProtoPublicKey(sdkVer)
				if err != nil {
					t.Fatalf("%v", err)
				}
				ret = append(ret, pk)
			}
			return ret
		}

		checkCorrectSerializationAndDeserialization(t, chainID, getKeys(),
			string0,
			string1,
			string2,
			string3,
			int64_0,
			int64_1,
			uint64_0,
			uint64_1,
		)

	})
}

*/
