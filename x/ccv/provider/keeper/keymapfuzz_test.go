package keeper_test

import (
	cryptoEd25519 "crypto/ed25519"
	"testing"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	cosmosEd25519 "github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	"github.com/cosmos/ibc-go/v3/testing/mock"
)

func FuzzKeyMapX(f *testing.F) {
	// go test -fuzz FuzzKeyMapX -fuzztime=2m keymapfuzz_test.go
	f.Fuzz(func(t *testing.T, chainID string, bz []byte) {
		bytesPerKey := 32
		if len(bz) < bytesPerKey {
			t.Skip()
		}
		i := 0
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
		_ = pk
	})
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
