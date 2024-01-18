package params

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
)

// SetAddressPrefixes builds the Config with Bech32 addressPrefix and publKeyPrefix for accounts, validators, and consensus nodes and verifies that addreeses have correct format.
// Not sealed yet
func SetAddressPrefixes(bech32Prefix string) {
	cfg := sdk.GetConfig()

	// bech32PrefixAccAddr defines the Bech32 prefix of an account's address
	bech32PrefixAccAddr := bech32Prefix
	// bech32PrefixAccPub defines the Bech32 prefix of an account's public key
	bech32PrefixAccPub := bech32Prefix + sdk.PrefixPublic
	// bech32PrefixValAddr defines the Bech32 prefix of a validator's operator address
	bech32PrefixValAddr := bech32Prefix + sdk.PrefixValidator + sdk.PrefixOperator
	// bech32PrefixValPub defines the Bech32 prefix of a validator's operator public key
	bech32PrefixValPub := bech32Prefix + sdk.PrefixValidator + sdk.PrefixOperator + sdk.PrefixPublic
	// bech32PrefixConsAddr defines the Bech32 prefix of a consensus node address
	bech32PrefixConsAddr := bech32Prefix + sdk.PrefixValidator + sdk.PrefixConsensus
	// bech32PrefixConsPub defines the Bech32 prefix of a consensus node public key
	bech32PrefixConsPub := bech32Prefix + sdk.PrefixValidator + sdk.PrefixConsensus + sdk.PrefixPublic

	cfg.SetBech32PrefixForAccount(bech32PrefixAccAddr, bech32PrefixAccPub)
	cfg.SetBech32PrefixForValidator(bech32PrefixValAddr, bech32PrefixValPub)
	cfg.SetBech32PrefixForConsensusNode(bech32PrefixConsAddr, bech32PrefixConsPub)

	cfg.Seal()
}
