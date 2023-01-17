package crypto

import (
	"encoding/binary"

	ibcmock "github.com/cosmos/ibc-go/v3/testing/mock"

	cryptoEd25519 "crypto/ed25519"
	"crypto/rand"

	sdkcryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	sdkcryptokeys "github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	sdkcryptotypes "github.com/cosmos/cosmos-sdk/crypto/types"
	sdktypes "github.com/cosmos/cosmos-sdk/types"
	sdkstakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	sdk "github.com/cosmos/cosmos-sdk/types"
	tmcrypto "github.com/tendermint/tendermint/crypto"
	tmprotocrypto "github.com/tendermint/tendermint/proto/tendermint/crypto"
	tmtypes "github.com/tendermint/tendermint/types"
)

// CryptoIdentity is a test helper for generating keys and addresses of
// various interfaces and types used by the SDK and Tendermint from a single
// 'root' private key.
type CryptoIdentity struct {
	// private key of crypto identity consensus address
	ibcmock.PV
	// operator address
	sdk.ValAddress
}

func NewCryptoIdentityFromBytesSeed(seed []byte) *CryptoIdentity {
	//lint:ignore SA1019 We don't care because this is only a test.

	// generate private key for consensus address
	consPrivKey := ibcmock.PV{PrivKey: &sdkcryptokeys.PrivKey{Key: cryptoEd25519.NewKeyFromSeed(seed)}}

	// randomize seed
	_, err := rand.Read(seed)
	if err != nil {
		panic(err)
	}

	// generate private key for operator address
	opPrivKey := &sdkcryptokeys.PrivKey{Key: cryptoEd25519.NewKeyFromSeed(seed)}

	return &CryptoIdentity{
		PV:         consPrivKey,
		ValAddress: sdk.ValAddress(opPrivKey.PubKey().Address()),
	}
}

func NewCryptoIdentityFromIntSeed(i int) *CryptoIdentity {
	iUint64 := uint64(i)
	seed := []byte("AAAAAAAAabcdefghijklmnopqrstuvwx") // 8+24 bytes
	binary.LittleEndian.PutUint64(seed[:8], iUint64)
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
	ret, err := sdkstakingtypes.NewValidator(v.SDKValOpAddress(), v.SDKPubKey(), sdkstakingtypes.Description{})
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

func (v *CryptoIdentity) SDKValOpAddress() sdktypes.ValAddress {
	return v.ValAddress
}

func (v *CryptoIdentity) SDKValConsAddress() sdktypes.ConsAddress {
	return sdktypes.ConsAddress(v.SDKPubKey().Address())
}
