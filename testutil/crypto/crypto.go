package crypto

import (
	cryptoEd25519 "crypto/ed25519"
	"encoding/binary"

	sdkcryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	sdkcryptoEd25519 "github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	sdkcryptoSecp256k1 "github.com/cosmos/cosmos-sdk/crypto/keys/secp256k1"
	sdkcryptotypes "github.com/cosmos/cosmos-sdk/crypto/types"
	sdktypes "github.com/cosmos/cosmos-sdk/types"
	sdkstakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	tmcrypto "github.com/cometbft/cometbft/crypto"
	tmprotocrypto "github.com/cometbft/cometbft/proto/tendermint/crypto"
	tmtypes "github.com/cometbft/cometbft/types"

	providertypes "github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
)

// CryptoIdentity is a test helper for generating keys and addresses of
// various interfaces and types used by the SDK and Tendermint from a single
// 'root' seed.
type CryptoIdentity struct {
	// private key for validators to run consensus
	consensus sdkcryptotypes.PrivKey
	// key for validator operator account
	operator sdkcryptotypes.PrivKey
}

func NewCryptoIdentityFromBytesSeed(seed []byte) *CryptoIdentity {
	//lint:ignore SA1019 We don't care because this is only a test.

	consKey := &sdkcryptoEd25519.PrivKey{Key: cryptoEd25519.NewKeyFromSeed(seed)} //nolint:staticcheck //  SA1019: sdkcryptoEd25519.PrivKey is deprecated: PrivKey defines a ed25519 private key. NOTE: ed25519 keys must not be used in SDK apps except in a tendermint validator context.
	opKey := sdkcryptoSecp256k1.GenPrivKeyFromSecret(seed)

	return &CryptoIdentity{
		consensus: consKey,
		operator:  opKey,
	}
}

func NewCryptoIdentityFromIntSeed(i int) *CryptoIdentity {
	iUint64 := uint64(i)
	seed := []byte("AAAAAAAAabcdefghijklmnopqrstuvwx") // 8+24 bytes
	binary.LittleEndian.PutUint64(seed[:8], iUint64)
	return NewCryptoIdentityFromBytesSeed(seed)
}

// GenMultipleCryptoIds generates and returns multiple CryptoIdentities from a starting int seed.
func GenMultipleCryptoIds(num, fromIntSeed int) []*CryptoIdentity {
	ids := make([]*CryptoIdentity, num)
	for i := 0; i < num; i++ {
		ids[i] = NewCryptoIdentityFromIntSeed(fromIntSeed + i)
	}
	return ids
}

func (v *CryptoIdentity) TMValidator(power int64) *tmtypes.Validator {
	return tmtypes.NewValidator(v.TMCryptoPubKey(), power)
}

func (v *CryptoIdentity) TMProtoCryptoPublicKey() tmprotocrypto.PublicKey {
	ret, err := sdkcryptocodec.ToCmtProtoPublicKey(v.ConsensusSDKPubKey())
	if err != nil {
		panic(err)
	}
	return ret
}

func (v *CryptoIdentity) TMCryptoPubKey() tmcrypto.PubKey {
	ret, err := sdkcryptocodec.ToCmtPubKeyInterface(v.ConsensusSDKPubKey())
	if err != nil {
		panic(err)
	}
	return ret
}

func (v *CryptoIdentity) SDKStakingValidator() sdkstakingtypes.Validator {
	ret, err := sdkstakingtypes.NewValidator(v.SDKValOpAddressString(), v.ConsensusSDKPubKey(), sdkstakingtypes.Description{})
	if err != nil {
		panic(err)
	}
	return ret
}

func (v *CryptoIdentity) SDKValOpAddressString() string {
	return sdktypes.ValAddress(v.OperatorSDKPubKey().Address()).String()
}

func (v *CryptoIdentity) ConsensusSDKPubKey() sdkcryptotypes.PubKey {
	return v.consensus.PubKey()
}

func (v *CryptoIdentity) OperatorSDKPubKey() sdkcryptotypes.PubKey {
	return v.operator.PubKey()
}

func (v *CryptoIdentity) SDKValOpAddress() sdktypes.ValAddress {
	return sdktypes.ValAddress(v.OperatorSDKPubKey().Address())
}

func (v *CryptoIdentity) SDKValConsAddress() sdktypes.ConsAddress {
	return sdktypes.ConsAddress(v.ConsensusSDKPubKey().Address())
}

// Returns the cons address of the crypto identity as a ProviderConsAddress.
// In most cases, one crypto identity should NOT be casted to both a ProviderConsAddress and ConsumerConsAddress.
// However, test intention is left to the caller.
func (v *CryptoIdentity) ProviderConsAddress() providertypes.ProviderConsAddress {
	return providertypes.NewProviderConsAddress(v.SDKValConsAddress())
}

// Returns the cons address of the crypto identity as a ConsumerConsAddress.
// In most cases, one crypto identity should NOT be casted to both a ProviderConsAddress and ConsumerConsAddress.
// However, test intention is left to the caller.
func (v *CryptoIdentity) ConsumerConsAddress() providertypes.ConsumerConsAddress {
	return providertypes.NewConsumerConsAddress(v.SDKValConsAddress())
}
