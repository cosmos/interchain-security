package crypto

import (
	"crypto/rand"

	"encoding/binary"

	ibcmock "github.com/cosmos/ibc-go/v3/testing/mock"

	cryptoEd25519 "crypto/ed25519"

	sdkcryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	sdkcryptokeys "github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	sdkcryptotypes "github.com/cosmos/cosmos-sdk/crypto/types"
	sdktypes "github.com/cosmos/cosmos-sdk/types"
	sdkstakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	tmcrypto "github.com/tendermint/tendermint/crypto"
	tmprotocrypto "github.com/tendermint/tendermint/proto/tendermint/crypto"
	tmtypes "github.com/tendermint/tendermint/types"
)

// CryptoIdentity is a test helper for generating keys and addresses of
// various interfaces and types used by the SDK and Tendermint from a single
// 'root' private key.
type CryptoIdentity struct {
	ibcmock.PV
}

func NewCryptoIdentityFromBytesSeed(seed []byte) CryptoIdentity {
	//lint:ignore SA1019 We don't care because this is only a test.
	privKey := ibcmock.PV{PrivKey: &sdkcryptokeys.PrivKey{Key: cryptoEd25519.NewKeyFromSeed(seed)}}
	return CryptoIdentity{PV: privKey}
}

func NewCryptoIdentityFromRandSeed() CryptoIdentity {
	b := make([]byte, 8)
	_, _ = rand.Read(b)
	seed := binary.BigEndian.Uint64(b)
	return NewCryptoIdentityFromIntSeed(seed)
}

func NewCryptoIdentityFromIntSeed(i uint64) CryptoIdentity {
	seed := []byte("AAAAAAAAabcdefghijklmnopqrstuvwx") // 8+24 bytes
	binary.LittleEndian.PutUint64(seed[:8], i)
	return NewCryptoIdentityFromBytesSeed(seed)
}

func (v *CryptoIdentity) ABCIAddressBytes() []byte {
	return v.SDKPubKey().Address()
}

func (v *CryptoIdentity) TMValidator(power int64) *tmtypes.Validator {
	return tmtypes.NewValidator(v.TMCryptoPubKey(), power)
}

func (v *CryptoIdentity) TMProtoCryptoPublicKey() tmprotocrypto.PublicKey {
	ret, err := sdkcryptocodec.ToTmProtoPublicKey(v.SDKPubKey())
	if err != nil {
		panic(err)
	}
	return ret
}

func (v *CryptoIdentity) TMCryptoPubKey() tmcrypto.PubKey {
	ret, err := v.GetPubKey()
	if err != nil {
		panic(err)
	}
	return ret
}

func (v *CryptoIdentity) SDKStakingValidator() sdkstakingtypes.Validator {
	ret, err := sdkstakingtypes.NewValidator(v.SDKValAddress(), v.SDKPubKey(), sdkstakingtypes.Description{})
	if err != nil {
		panic(err)
	}
	return ret
}

func (v *CryptoIdentity) SDKPubKey() sdkcryptotypes.PubKey {
	tmcryptoPubKey := v.TMCryptoPubKey()
	ret, err := sdkcryptocodec.FromTmPubKeyInterface(tmcryptoPubKey)
	if err != nil {
		panic(err)
	}
	return ret
}

func (v *CryptoIdentity) SDKValAddressString() string {
	return v.TMCryptoPubKey().Address().String()
}

func (v *CryptoIdentity) SDKValAddress() sdktypes.ValAddress {
	ret, err := sdktypes.ValAddressFromHex(v.SDKValAddressString())
	if err != nil {
		panic(err)
	}
	return ret
}

func (v *CryptoIdentity) SDKConsAddress() sdktypes.ConsAddress {
	return sdktypes.GetConsAddress(v.SDKPubKey())
}
