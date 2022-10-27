package sample

import (
	"encoding/binary"

	cryptoEd25519 "crypto/ed25519"

	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/ibc-go/v3/testing/mock"

	tmprotocrypto "github.com/tendermint/tendermint/proto/tendermint/crypto"
)

// AccAddress returns a sample account address
func AccAddress() string {
	pk := ed25519.GenPrivKey().PubKey()
	addr := pk.Address()
	return sdk.AccAddress(addr).String()
}

func GetTMCryptoPublicKeyFromSeed(i uint64) (mock.PV, tmprotocrypto.PublicKey) {

	fromSeed := func(seed []byte) (mock.PV, tmprotocrypto.PublicKey) {
		//lint:ignore SA1019 We don't care because this is only a test.
		privKey := mock.PV{PrivKey: &ed25519.PrivKey{Key: cryptoEd25519.NewKeyFromSeed(seed)}}
		pubKey, err := privKey.GetPubKey()
		if err != nil {
			panic(err)
		}
		sdkKey, err := cryptocodec.FromTmPubKeyInterface(pubKey)
		if err != nil {
			panic(err)
		}
		tmProtoKey, err := cryptocodec.ToTmProtoPublicKey(sdkKey)
		if err != nil {
			panic(err)
		}
		return privKey, tmProtoKey
	}

	seed := []byte("AAAAAAAAabcdefghijklmnopqrstuvwx") // 8+24 bytes
	binary.LittleEndian.PutUint64(seed[:8], i)
	return fromSeed(seed)
}
