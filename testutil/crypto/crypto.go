package crypto

import (
	"bytes"
	"encoding/binary"
	"encoding/hex"
	"fmt"
	"math/rand"

	ibcmock "github.com/cosmos/ibc-go/v3/testing/mock"

	cryptoEd25519 "crypto/ed25519"

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
	ibcmock.PV
	OpAddress sdk.ValAddress
}

func NewCryptoIdentityFromBytesSeed(seed []byte) *CryptoIdentity {
	//lint:ignore SA1019 We don't care because this is only a test.
	privKey := ibcmock.PV{PrivKey: &sdkcryptokeys.PrivKey{Key: cryptoEd25519.NewKeyFromSeed(seed)}}
	rand.Uint64()
	sdk.ValAddressFromHex("")
	return &CryptoIdentity{PV: privKey}
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

func (v *CryptoIdentity) SDKStakingOperator() sdktypes.ValAddress {
	return v.SDKStakingValidator().GetOperator()
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

func (v *CryptoIdentity) SDKValAddress() sdktypes.ValAddress {
	return sdktypes.ValAddress(v.SDKPubKey().Address())
}

func (v *CryptoIdentity) SDKConsAddress() sdktypes.ConsAddress {
	return sdktypes.ConsAddress(v.SDKPubKey().Address())
}

func CreateOpAddressFromByteSeed(seed []byte) {

	opAddressSeed := make([]byte, 40)
	copy(opAddressSeed, seed)
	// add 8 random bytes to seed
	// binary.LittleEndian.PutUint64(opAddressSeed[32:], rand.Uint64())
	// seedHex := hex.EncodeToString(opAddressSeed)
	var buffer bytes.Buffer

	buffer.WriteString(hex.EncodeToString(opAddressSeed[:20]))

	res, err := sdk.ValAddressFromHex(buffer.String())
	if err != nil {
		panic(err)
	}
	fmt.Println(res.String())
	fmt.Println(len(res.Bytes()))

	// account addresss generation taken from cosmos-sdk/simapp/test_helpers

	// var addresses []sdk.ValAddress
	// var buffer bytes.Buffer

	// var seed []byte

	// buffer.WriteString("A58856F0FD53BF058B4909A21AEC019107BA6") // base address string
	// buffer.WriteString(string(rand.))
}
