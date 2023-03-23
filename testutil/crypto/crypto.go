package crypto

import (
	"encoding/binary"

	cryptoEd25519 "crypto/ed25519"

	sdkcryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	sdkcryptoEd25519 "github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	sdkcryptoSecp256k1 "github.com/cosmos/cosmos-sdk/crypto/keys/secp256k1"
	sdkcryptotypes "github.com/cosmos/cosmos-sdk/crypto/types"
	sdktypes "github.com/cosmos/cosmos-sdk/types"
	sdkstakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"

	tmcrypto "github.com/tendermint/tendermint/crypto"
	tmprotocrypto "github.com/tendermint/tendermint/proto/tendermint/crypto"
	tmtypes "github.com/tendermint/tendermint/types"
)

// Identity is a test helper for generating keys and addresses of
// various interfaces and types used by the SDK and Tendermint from a single
// 'root' seed.
type Identity struct {
	// private key for validators to run consensus
	consensus sdkcryptotypes.PrivKey
	// key for validator operator account
	operator sdkcryptotypes.PrivKey
}

func NewCryptoIdentityFromBytesSeed(seed []byte) *Identity {
	//lint:ignore SA1019 We don't care because this is only a test.

	consKey := &sdkcryptoEd25519.PrivKey{Key: cryptoEd25519.NewKeyFromSeed(seed)} //nolint:staticcheck
	opKey := sdkcryptoSecp256k1.GenPrivKeyFromSecret(seed)

	return &Identity{
		consensus: consKey,
		operator:  opKey,
	}
}

func NewCryptoIdentityFromIntSeed(i int) *Identity {
	iUint64 := uint64(i)
	seed := []byte("AAAAAAAAabcdefghijklmnopqrstuvwx") // 8+24 bytes
	binary.LittleEndian.PutUint64(seed[:8], iUint64)
	return NewCryptoIdentityFromBytesSeed(seed)
}

func (v *Identity) TMValidator(power int64) *tmtypes.Validator {
	return tmtypes.NewValidator(v.TMCryptoPubKey(), power)
}

func (v *Identity) TMProtoCryptoPublicKey() tmprotocrypto.PublicKey {
	ret, err := sdkcryptocodec.ToTmProtoPublicKey(v.ConsensusSDKPubKey())
	if err != nil {
		panic(err)
	}
	return ret
}

func (v *Identity) TMCryptoPubKey() tmcrypto.PubKey {
	ret, err := sdkcryptocodec.ToTmPubKeyInterface(v.ConsensusSDKPubKey())
	if err != nil {
		panic(err)
	}
	return ret
}

func (v *Identity) SDKStakingValidator() sdkstakingtypes.Validator {
	ret, err := sdkstakingtypes.NewValidator(v.SDKValOpAddress(), v.ConsensusSDKPubKey(), sdkstakingtypes.Description{})
	if err != nil {
		panic(err)
	}
	return ret
}

func (v *Identity) ConsensusSDKPubKey() sdkcryptotypes.PubKey {
	return v.consensus.PubKey()
}

func (v *Identity) OperatorSDKPubKey() sdkcryptotypes.PubKey {
	return v.operator.PubKey()
}

func (v *Identity) SDKValOpAddress() sdktypes.ValAddress {
	return sdktypes.ValAddress(v.OperatorSDKPubKey().Address())
}

func (v *Identity) SDKValConsAddress() sdktypes.ConsAddress {
	return sdktypes.ConsAddress(v.ConsensusSDKPubKey().Address())
}

// Returns the cons address of the crypto identity as a ProviderConsAddress.
// In most cases, one crypto identity should NOT be casted to both a ProviderConsAddress and ConsumerConsAddress.
// However, test intention is left to the caller.
func (v *Identity) ProviderConsAddress() providertypes.ProviderConsAddress {
	return providertypes.NewProviderConsAddress(v.SDKValConsAddress())
}

// Returns the cons address of the crypto identity as a ConsumerConsAddress.
// In most cases, one crypto identity should NOT be casted to both a ProviderConsAddress and ConsumerConsAddress.
// However, test intention is left to the caller.
func (v *Identity) ConsumerConsAddress() providertypes.ConsumerConsAddress {
	return providertypes.NewConsumerConsAddress(v.SDKValConsAddress())
}
