package crypto

import (
	"encoding/binary"

	"github.com/cosmos/ibc-go/v3/testing/mock"

	cryptoEd25519 "crypto/ed25519"

	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"

	sdkcryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	sdkcryptotypes "github.com/cosmos/cosmos-sdk/crypto/types"

	tmcrypto "github.com/tendermint/tendermint/crypto"
	tmprotocrypto "github.com/tendermint/tendermint/proto/tendermint/crypto"
)

type Validator struct {
	mock.PV
}

func NewValidatorFromBytesSeed(seed []byte) Validator {
	//lint:ignore SA1019 We don't care because this is only a test.
	privKey := mock.PV{PrivKey: &ed25519.PrivKey{Key: cryptoEd25519.NewKeyFromSeed(seed)}}
	return Validator{PV: privKey}
}

func NewValidatorFromIntSeed(i int) Validator {
	iUint64 := uint64(i)
	seed := []byte("AAAAAAAAabcdefghijklmnopqrstuvwx") // 8+24 bytes
	binary.LittleEndian.PutUint64(seed[:8], iUint64)
	return NewValidatorFromBytesSeed(seed)
}

func (v *Validator) TMProtoCryptoPublicKey() tmprotocrypto.PublicKey {
	ret, err := sdkcryptocodec.ToTmProtoPublicKey(v.SDKPubKey())
	if err != nil {
		panic(err)
	}
	return ret
}

func (v *Validator) TMCryptoPubKey() tmcrypto.PubKey {
	ret, err := v.GetPubKey()
	if err != nil {
		panic(err)
	}
	return ret
}

func (v *Validator) SDKPubKey() sdkcryptotypes.PubKey {
	tmcryptoPubKey := v.TMCryptoPubKey()
	ret, err := sdkcryptocodec.FromTmPubKeyInterface(tmcryptoPubKey)
	if err != nil {
		panic(err)
	}
	return ret
}
