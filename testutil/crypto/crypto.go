package crypto

import (
	"encoding/binary"

	"github.com/cosmos/ibc-go/v3/testing/mock"

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

type Validator struct {
	mock.PV
}

func NewValidatorFromBytesSeed(seed []byte) Validator {
	//lint:ignore SA1019 We don't care because this is only a test.
	privKey := mock.PV{PrivKey: &sdkcryptokeys.PrivKey{Key: cryptoEd25519.NewKeyFromSeed(seed)}}
	return Validator{PV: privKey}
}

func NewValidatorFromIntSeed(i int) Validator {
	iUint64 := uint64(i)
	seed := []byte("AAAAAAAAabcdefghijklmnopqrstuvwx") // 8+24 bytes
	binary.LittleEndian.PutUint64(seed[:8], iUint64)
	return NewValidatorFromBytesSeed(seed)
}

func (v *Validator) ABCIAddressBytes() []byte {
	return v.SDKPubKey().Address()
}

func (v *Validator) TMValidator(power int64) *tmtypes.Validator {
	return tmtypes.NewValidator(v.TMCryptoPubKey(), power)
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

func (v *Validator) SDKStakingValidator() sdkstakingtypes.Validator {
	ret, err := sdkstakingtypes.NewValidator(v.SDKValAddress(), v.SDKPubKey(), sdkstakingtypes.Description{})
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

func (v *Validator) SDKValAddressString() string {
	return v.TMCryptoPubKey().Address().String()
}

func (v *Validator) SDKValAddress() sdktypes.ValAddress {
	ret, err := sdktypes.ValAddressFromHex(v.SDKValAddressString())
	if err != nil {
		panic(err)
	}
	return ret
}

func (v *Validator) SDKConsAddress() sdktypes.ConsAddress {
	return sdktypes.GetConsAddress(v.SDKPubKey())
}
